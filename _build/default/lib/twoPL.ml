open Mapping

let checkNewRGroupSetEmpty newRGroupSet key roMap= 
  if List.length newRGroupSet = 0 then 
      IntMap.remove key roMap
  else IntMap.add key newRGroupSet roMap
  (* newRoMap = checkNewRGroupSetEmpty newRGroupSet key roMap
    ensures if List.length newRGroupSet = 0 then
              newRoMap.IntMap.mem key = false   
            else 
              List.length (roMap.IntMap.view key) > List.length (newRoMap.IntMap.view key) 
  *)


let rec ropListTrasverse ropList roMap key (rGroup:ResourceGroup.resourceGroup) lastlock set= 
 match ropList with 
 | [] -> roMap
 | (x:Roperation.rOp) :: xs ->
    let opCode = x.op in
    if opCode = 7 then (* opCode = release*)
      let newRGroupSet = List.filter ( fun x -> x.ResourceGroup.id <> rGroup.ResourceGroup.id ) set in
      let newRoMap = checkNewRGroupSetEmpty newRGroupSet key roMap in 
      let newRoMap = ROperationsMapGeneration.insertR (lastlock+1) rGroup newRoMap in 
      ropListTrasverse xs newRoMap key rGroup lastlock set
    else ropListTrasverse xs roMap key rGroup lastlock set
  (* newRoMap = ropListTrasverse ropList roMap key (rGroup:ResourceGroup.resourceGroup) lastlock set
      variant ropList
      ensures forall rop. List.mem rop ropList ->
      rop.ResourceOperation.op = 7 -> 
        List.length (newRoMap.IntMap.view (lastlock+1)) > List.length (roMap.IntMap.view (lastlock+1))

  *)

(*Função que itera o roMap e determina quais as operações de Release que são realizadas antes do ultima operação de lock e move essas operações de sitio*)
let rec findGroups (roMap:ResourceGroup.resourceGroup list IntMap.t) keys lastlock= 
  match keys with
  | [] -> roMap
  | x :: xs ->
    let set = IntMap.find x roMap in
    if x < lastlock then 

      let rec iterateSet (set:ResourceGroup.resourceGroup list) roMap key= 
        match set with 
        | [] -> roMap 
        | x :: xs -> 
          let rGroup = x in 
          let newRoMap = ropListTrasverse x.ropList roMap key rGroup lastlock set in 
          iterateSet xs newRoMap key in 
         
    let newRoMap = iterateSet set roMap x in 
    findGroups newRoMap xs lastlock
    else findGroups roMap xs lastlock
    
 
let rec getLastLock (ropList:Roperation.rOp list) lastlock (key:int)= 
    match ropList with 
    | [] -> lastlock
    | x :: xs -> 
      let opCode = x.op in
        if opCode = 5 || opCode = 2 || opCode = 4 then (*op == OpCode.UPGRADE || op == OpCode.READ || op == OpCode.EXCLUSIVE*)
          getLastLock xs key key
        else getLastLock xs lastlock key
    (* newlastlock =  getLastLock ropList lastlock key
        variant ropList
        ensures forall rop. List.mem rop ropList ->
          rop.ResourceOperation.op = 5 || rop.ResourceOperation.op = 2 || rop.ResourceOperation.op = 4 ->
            newLastLock >= lastlock
    *)

let rec iterate keys roMap (lastlock: int)= 
  match keys with 
  | [] -> lastlock
  | x :: xs ->
    let set = IntMap.find x roMap in

    let rec iterateSet set (lastlock:int) key= 
      match set with 
      | [] -> lastlock
      | (x:ResourceGroup.resourceGroup) :: xs -> 
      let newLastlock = getLastLock x.ropList lastlock key in 
      iterateSet xs newLastlock key in 
      
    let newLastlock = iterateSet set lastlock x in 
    iterate xs roMap newLastlock

(*Função que itera o roMap e determina qual é o ultima operação que faz um lock no metodo*)
let twoPhaseLocking (roMap:ResourceGroup.resourceGroup list IntMap.t)= 
  let bindings = IntMap.bindings roMap in
  let keys = List.map (fun (k, _) -> k) bindings in
  let newLastlock = iterate keys roMap 0 in 
  let roMap = findGroups roMap keys newLastlock in 
  roMap
