open Mapping
open Resource
open Roperation
open ResourceGroup

module Parameters = Set.Make(Int)

module Handled = Set.Make(Int)


let [@logic] conflict opCode1 opCode2= 
  if (opCode1 = 7 || opCode1 = 6) || (opCode2 = 7 || opCode2 = 6) then false
  else 
    begin
      if ((opCode1 = 4 || opCode1 = 5) || (opCode2 = 4 || opCode2 = 5)) then 
        true else false
    end
    (*@b = conflict opCode1 opCode2
    requires opCode1 > -1 && opCode1 < 8
    requires opCode2 > -1 && opCode2 < 8
    ensures b = true  <-> ((opCode1 <> 7 && opCode1 <> 6) && (opCode2 <> 7 && opCode2 <> 6)) && ((opCode1 = 4 || opCode1 = 5) || (opCode2 = 4 || opCode2 = 5))
  *)

let removeFromGroupSet label rGroup rGroupSet roMap= 
  let newRGroupSet = List.filter ( fun x -> x.ResourceGroup.id <> rGroup.ResourceGroup.id ) rGroupSet in
  let newRoMap = IntMap.add label newRGroupSet roMap in 
  newRoMap     
  (*@newROMap = removeFromGroupSet label rGroup rGroupSet roMap
     ensures forall rgroup. List.mem rgroup rGroupSet ->
              exists newRGroupSet.
              if rgroup.id <> rGroup.id then
              List.mem rgroup newRGroupSet = true
              else
              List.mem rGroup newRGroupSet = false
              &&
              IntMap.mem label newROMap && newROMap.IntMap.view label = newRGroupSet
              *)
             
let addNewRGroup label roMap rGroup = 
    print_string "ENTROU ADD NEWRGROUP";print_string "\n";
    try let (rGroupSet: ResourceGroup.resourceGroup list) = IntMap.find label roMap in 
      let newRGroupSet = List.filter ( fun x -> x.ResourceGroup.id <> rGroup.ResourceGroup.id ) rGroupSet in
      Printf.printf "rGroup id = %d\n" rGroup.id;
      let newRGroupSet = newRGroupSet @ [rGroup] in 
      let newRoMap = IntMap.add label newRGroupSet roMap in 
      Printf.printf "label = %d\n" label;
      Printf.printf "rGroupList length = %d\n" (List.length newRGroupSet);
      newRoMap
    with Not_found -> (
      roMap
    )
    (*@newRoMap = addNewRGroup label roMap rGroup
       ensures if IntMap.mem label roMap then 
                let rGroupSet = roMap.IntMap.view label in
                exists newRGroupSet. 
                (IntMap.mem label newRoMap && newRGroupSet = newRoMap.IntMap.view label) && 
                List.mem rGroup newRGroupSet
                else
                  IntMap.mem label roMap = false && roMap = newRoMap *)

  let ropListEmpty label roMap rGroup= 
    try let (rGroupSet: ResourceGroup.resourceGroup list) = IntMap.find label roMap in 
    if List.length rGroupSet = 1 then 
      begin
      let newRoMap = IntMap.remove label roMap in 
      newRoMap
      end
    else 
      removeFromGroupSet label rGroup rGroupSet roMap
    with Not_found -> (
      roMap
    )
    (*@newRoMap = ropListEmpty label roMap rGroup
      ensures if IntMap.mem label roMap then
        let rGroupSet = roMap.IntMap.view label in
        if List.length rGroupSet = 1 then 
          IntMap.mem label newRoMap = false
        else
           forall rgroup. List.mem rgroup rGroupSet ->
             exists newRGroupSet.
              if rgroup.id <> rGroup.id then
              List.mem rgroup newRGroupSet = true
              else
              List.mem rGroup newRGroupSet = false
              &&
              IntMap.mem label newRoMap && newRoMap.IntMap.view label = newRGroupSet
        else IntMap.mem label roMap = false && roMap = newRoMap
    *)


(*Function that removes a rop from the rGroup argument, checks if the ropList is 0 and if it is then finds the rGroupSet from
   the label, and if that rGroup is the only one associated with that label then removes the label from the map.
    If there's more rGroup then it filters the list in order to remove that rGroup from it and adds it back into the map*)
let removeR label rGroup roMap =
  if List.length rGroup.ResourceGroup.ropList = 0 then
      ropListEmpty label roMap rGroup
  else
    addNewRGroup label roMap rGroup
  (*@newRoMap =  removeR label rGroup roMap 
    ensures if List.length rGroup.ResourceGroup.ropList = 0 then
        if IntMap.mem label roMap then
        let rGroupSet = roMap.IntMap.view label in
        if List.length rGroupSet = 1 then 
          IntMap.mem label newRoMap = false
        else
           forall rgroup. List.mem rgroup rGroupSet ->
              exists newRGroupSet.
              if rgroup.id <> rGroup.id then
              List.mem rgroup newRGroupSet = true
              else
              List.mem rGroup newRGroupSet = false
              &&
              IntMap.mem label newRoMap && newRoMap.IntMap.view label = newRGroupSet
        else IntMap.mem label roMap = false && roMap = newRoMap
      else 
       if IntMap.mem label roMap then 
                let rGroupSet = roMap.IntMap.view label in
                exists newRGroupSet. 
                (IntMap.mem label newRoMap && newRGroupSet = newRoMap.IntMap.view label) && 
                List.mem rGroup newRGroupSet
                else
                  IntMap.mem label roMap = false && roMap = newRoMap 
  *)
    
  (* Recursive function that trasverses the set and for each rGroup calls the getResult function
     and if sbe = true then calls the remove function
      Returns the roMap, founSBE and finished*)
  let rec checkSBE (set:ResourceGroup.resourceGroup list) resource2 label roMap foundSBE finished= 
    match set with 
    | [] -> roMap, foundSBE, finished
    | x :: xs -> 
      if not finished then
      let ropList = x.ResourceGroup.ropList in 
      let (sbe:bool) = ResourceGroup.getResult ropList {op= 3; r= resource2} in 
      if sbe then
        begin
          let (rOp:rOp) = { op = 3; r = resource2} in 
          let rGroup = remove rOp x in
          let newRoMap = removeR label rGroup roMap in
          checkSBE xs resource2 label newRoMap true true
        end
      else checkSBE xs resource2 label roMap foundSBE finished
    else checkSBE xs resource2 label roMap foundSBE finished
  (*@newRoMap, foundsbe, finishedRes = checkSBE set resource2 label roMap foundSBE finished
      variant set
      ensures  match set with 
          | [] -> newRoMap = roMap && foundsbe = foundSBE && finishedRes = finished
          | x :: xs -> 
            if not finished then
            let ropList = x.ropList in 
              let sbe = ResourceGroup.getResult ropList {op= 3; r= resource2} in 
            if sbe then
              let rOp = { op = 3; r = resource2} in 
              let rGroup = remove rOp x in
              (if List.length rGroup.ResourceGroup.ropList = 0 then
            if IntMap.mem label roMap then
              let rGroupSet = roMap.IntMap.view label in
            if List.length rGroupSet = 1 then 
            IntMap.mem label newRoMap = false
            else
            forall rgroup. List.mem rgroup rGroupSet ->
              exists newRGroupSet.
              if rgroup.id <> rGroup.id then
              List.mem rgroup newRGroupSet = true
              else
              List.mem rGroup newRGroupSet = false
              &&
              IntMap.mem label newRoMap && newRoMap.IntMap.view label = newRGroupSet
        else IntMap.mem label roMap = false
      else 
       if IntMap.mem label roMap then 
                let rGroupSet = roMap.IntMap.view label in
                exists newRGroupSet. 
                (IntMap.mem label newRoMap && newRGroupSet = newRoMap.IntMap.view label) && 
                List.mem rGroup newRGroupSet
                else
                  IntMap.mem label roMap = false  ) 
          else true
        else true


     *)

      
(* Function that start by calling the keysCycle function and then if foundSBE = true then it changes the values of the
   newROperations *)
let outerLoop keys label2 roMap resource2 rOperation2= 
    let newROperation2 = ref rOperation2 in 

    (* Recursive function that trasverses the keys and for each key calls the function checkSBE
       Returns the new roMap and the new FoundSBE*)
    let rec keysCycle keys roMap finished foundSBE label2=
      match keys with
      | [] -> roMap,foundSBE
      | x :: xs ->
        try let set = IntMap.find label2 roMap in
          let newRoMap, newFoundSBE, newFinished = checkSBE set resource2 x roMap foundSBE finished in 
          if finished then 
            newRoMap,foundSBE
          else 
            keysCycle xs newRoMap newFoundSBE newFinished label2
        with Not_found ->(
          keysCycle xs roMap finished foundSBE label2
        ) in 
        (*roMap,foundSBE = keysCycle keys roMap finished foundSBE label2 *)
        
    let newRoMap, foundSBE = keysCycle keys roMap false false label2 in
    if foundSBE then 
      newROperation2 := {op = 4; r = resource2}
    else ();
    !newROperation2, newRoMap
    (*  newroperation2, newromap = outerLoop keys label2 roMap resource2 rOperation2 
        
    *)
    let typeConflict (resource1:ResourceClass.resource) (resource2:ResourceClass.resource) : bool = 
      resource1.ResourceClass.nature == resource2.ResourceClass.nature && 
      resource1.ResourceClass.ty == resource2.ResourceClass.ty
      (*result = typeConflict resource1 resource2
        ensures result = true <-> resource1.ResourceClass.nature = resource2.ResourceClass.nature && 
        resource1.ResourceClass.ty = resource2.ResourceClass.ty
      *)

(* Function that calls the function conflict between 2 rop and if all the conditions are met,
   adds the resource2 into the handled set and if the rOperation2 = 5 calls the outerloop function
   Returns the newROperation2, newRoMap and newHandled*)
let checkConflict hasR2 rOp1 rOperation2 r1 r2  parameters label2 roMap handled keys= 
  let newROperation2 = ref rOperation2 in
  let newHandled = ref handled in
  let newRoMap = ref roMap in
  if hasR2 == false && (conflict rOp1 rOperation2.op) && (typeConflict r1 r2) && Parameters.mem r2.ResourceClass.position parameters && 
    IntMap.mem label2 roMap then
    begin 
      newHandled := Handled.add r2.ResourceClass.position handled;
      if rOperation2.op = 5 then
        let a,b  = outerLoop keys label2 roMap r2.ResourceClass.position rOperation2 in
        newROperation2 := a; 
        newRoMap := b;
      else ()
  end
  else ();
  !newROperation2, !newRoMap, !newHandled
  (*  newROperation2, newRoMap, newHandled = checkConflict hasR2 rOp1 rOperation2 r1 r2 resource2 parameters label2 roMap handled keys
     ensures (hasR2 = false && conflict rOp1 rOperation2.op && r1 == r2 && Parameters.mem resource2 parameters && 
        ResourceOperationsMap.mem label2 roMap) -> Handled.mem resource2 newHandled
     ensures (hasR2 = false && conflict rOp1 rOperation2.op && r1 == r2 && Parameters.mem resource2 parameters && 
        ResourceOperationsMap.mem label2 roMap) && rOperation2.op = 5 -> 
          let a,b  = outerLoop keys label2 roMap resource2 rOperation2 in
          (newROperation2 = a && newRoMap = b)
    *)
  
(* Function that finds the set for a label, then removes a rGroup from that set and adds the newRGroup to it.
   Then, adds this newSet back into the roMap and calls the function remove.
   Returns the new roMap*)
let newRoMapCreation label1 roMap rGroup1 newrGroup1 label2 rGroup2 rOperation2=
  try let set = IntMap.find label1 roMap in 
  let newSet = List.filter (fun x -> x <> rGroup1 ) set in 
  let newSet = newSet @ [newrGroup1] in 
  let newRoMap = IntMap.add label1 newSet roMap in
  let rGroup2 = remove rOperation2 rGroup2 in
  let newRoMap = removeR label2 rGroup2 newRoMap in
  newRoMap
  with Not_found ->(
    roMap
  )

(*Recursive function that trasverses the ropList and for each rop finds the resource, checks if it's already in handled and
   calls the checkConflict function.
  Then, adds a new rop to the to the rGroup and calls the function newRoMapCreation
  Returns the roMap*)
let rec ropListCycle ropList roMap resourceMap handled rOp1 r1 parameters label2 rGroup1 label1 keys rGroup2=  
  match ropList with
  | [] -> roMap
  | x :: xs -> 
    let resource2 =  x.r in
    try let r2 = IntMap.find x.r resourceMap in 
    let hasR2 = Handled.mem resource2 handled in 
    let newROperation2,newRoMap,newHandled = checkConflict hasR2 rOp1 x r1 r2 parameters label2 roMap handled keys in 
    let newrGroup1 = ResourceGroup.add newROperation2 rGroup1 in 
    let newRoMap = newRoMapCreation label1 newRoMap rGroup1 newrGroup1 label2 rGroup2 newROperation2 in 
    ropListCycle xs newRoMap resourceMap newHandled rOp1 r1 parameters label2 newrGroup1 label1 keys rGroup2
    with Not_found -> (
    ropListCycle xs roMap resourceMap handled rOp1 r1 parameters label2 rGroup1 label1 keys rGroup2
  )

(* Recursive function that trasverses the keys and for each keys finds the corresponding set and
  calls the cycle function. Returns the new roMap *)
let rec checkGrouping keys rOp1 (r1:ResourceClass.resource) (rGroup1:ResourceGroup.resourceGroup) label1 (roMap:ResourceGroup.resourceGroup list IntMap.t) 
parameters handled (resourceMap:ResourceClass.resource IntMap.t) =
match keys with 
| [] -> roMap
| x :: xs -> 
  let label2 = x in
  try let set = IntMap.find label2 roMap in

  (* Recursive function that trasverses the set list and for each rGroup calls the ropListCycle function
     Returns the new roMap*)
  let rec cycle (set:ResourceGroup.resourceGroup list) roMap= 
    match set with 
    | [] -> roMap
    | x :: xs ->
    let newRoMap = ropListCycle x.ResourceGroup.ropList roMap resourceMap handled rOp1 r1 parameters label2 rGroup1 label1 keys x in 
    cycle xs newRoMap in

  let newRoMap = cycle set roMap in 
  checkGrouping xs rOp1 r1 rGroup1 label1 newRoMap parameters handled resourceMap
    with Not_found -> (
      checkGrouping xs rOp1 r1 rGroup1 label1 roMap parameters handled resourceMap
    )

(*Function that trasverses the ropList and for each rop does a check. If the check is true, then adds a resource to
   the handled set and calls the checkGrouping function for all the groupsAhead*)
let rec condition2ndResource rGroup ropList roMap resourceMap parameters label handled keys= 
  let newRoMap = ref roMap in
  match ropList with
  | [] -> roMap
  | x :: xs ->
    let resourceId = x.r in
    try let (resource1:ResourceClass.resource) = IntMap.find resourceId resourceMap in 

    if (x.op = 4 || x.op = 5 || 
      x.op = 3 || x.op = 2 ) && Parameters.mem resourceId parameters
      && IntMap.mem label roMap then

        begin
        let handled =  Handled.empty in
        let newHandled = Handled.add resourceId handled in 
        let groupsAhead = List.filter ( fun x -> x > label ) keys in
        
        newRoMap := checkGrouping groupsAhead x.op resource1 rGroup label roMap parameters newHandled resourceMap;
        condition2ndResource rGroup xs roMap resourceMap parameters label newHandled keys
        end

    else  condition2ndResource rGroup xs roMap resourceMap parameters label handled keys
    with Not_found -> (
      condition2ndResource rGroup xs roMap resourceMap parameters label handled keys
  )

  
(* Recursive function that trasverses the keys and obtains the set of a certain key and calls
  the setTransverse function*)
let rec resource1Cycle keys (roMap:ResourceGroup.resourceGroup list IntMap.t) parameters handled resourceMap= 
 
  match keys with 
  | [] -> roMap
  | x :: xs ->
    let label = x in
    try let set = IntMap.find label roMap in
 
    (* Recursive function that trasverses the set list and for each resourcegroup calls the condition2ndResource funtion*)
    let rec setTransverse set roMap = 
      match set with 
      | [] -> roMap
      | x :: xs -> 
      let newRoMap = condition2ndResource x x.ResourceGroup.ropList roMap resourceMap parameters label handled keys in
      setTransverse xs newRoMap in

    let newRoMap = setTransverse set roMap in 
    resource1Cycle xs newRoMap parameters handled resourceMap
    with Not_found ->(
      resource1Cycle xs roMap parameters handled resourceMap
      )
  
 (*Recursive function that trasverses the ropList and for each rop, gets his resource and adds it to the set.
     Returns the new parameters set*)
     let rec addParameters ropList parameters resourceMap= 
     match ropList with 
     | [] -> parameters
     | x :: xs -> 
         try let (resource: ResourceClass.resource) = IntMap.find x.r resourceMap in 
         if resource.ResourceClass.isParameter then 
          let newParameters = Parameters.add x.r parameters in
          addParameters xs newParameters resourceMap
         else 
          addParameters xs parameters resourceMap
        with Not_found ->( 
          addParameters xs parameters resourceMap
        )
     (*newParameters = addParameters ropList parameters resourceMap
        variant ropList
        ensures forall rop. List.mem rop ropList ->
          let resource = resourceMap.IntMap.view rop.r && IntMap.mem x.r resourceMap &&
          resource.ResourceClass.isParameter ->
          exists p.
          Parameters.mem p newParameters && rop.r = p
     *)

  (*Recursive function that trasverses the set list and for each group calls 
    addParameters and returns the new parameters set*)
    let rec findRGroup (set : ResourceGroup.resourceGroup list) (parameters : Parameters.t) resourceMap: Parameters.t =
      match set with
      | [] -> parameters
      | x :: xs -> 
        let newParameters = addParameters x.ResourceGroup.ropList parameters resourceMap in
        findRGroup xs newParameters resourceMap
        (* @ newParameters = findRGroup set parameters resourceMap
            requires forall rg. List.mem rg set -> rg.ropList <> []
            ensures forall rg. List.mem rg set ->
              forall rop. List.mem rop rg.ropList ->
                 exists p.
                Parameters.mem p newParameters && rop.r = p
        *)
    

(* Recursive function that trasverses the keys list and if key = -1 then we call findRGroup and return the newParameters Set*)
let rec addToParameters keys (parameters: Parameters.t) (roMap:ResourceGroup.resourceGroup list IntMap.t) resourceMap= 
  match keys with
  | [] -> parameters
  | x :: xs -> 
    try
      let set = IntMap.find x roMap in
      let newParameters = findRGroup set parameters resourceMap in
      addToParameters xs newParameters roMap resourceMap
    with Not_found ->(
      addToParameters xs parameters roMap resourceMap
  )
   
  

(* Função que recebe um resourceOperation map, separa as suas keys e values e chama a função addParameters*)
let parameterGrouping (roMap:ResourceGroup.resourceGroup list IntMap.t) 
(resourceMap:ResourceClass.resource IntMap.t) = 
  let bindings = IntMap.bindings roMap in
  let keys = List.map (fun (k, _) -> k) bindings in
  let handled = Handled.empty in
  let parameters = Parameters.empty in
  let newParameters = addToParameters keys parameters roMap resourceMap in 
  let newRoMap = resource1Cycle keys roMap newParameters handled resourceMap in
  newRoMap
