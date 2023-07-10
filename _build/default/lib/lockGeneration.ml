open Roperation
open Mapping
open Resource
open ResourceGroup

let rec checkGroupsLastRelease (set:resourceGroup list) guard  = 
   match set with 
   | [] -> false
   | x :: xs -> 

      let rec checkRopList guard (ropList:rOp list) = 
         match ropList with
         | [] -> false
         | x :: xs ->
            if x.r = guard && x.op = 7 then 
               true
            else 
               checkRopList guard xs in
      (* @b = checkRopList guard ropList
         requires guard >= -1
         ensures true <-> (exists x. List.mem x ropList && x.op = 7)  *)
         
         if (checkRopList guard x.ResourceGroup.ropList ) then
            true
         else checkGroupsLastRelease xs guard 
      (* @b = checkGroupsLastWrite set guard
         requires guard >= -1
         ensures true <-> exists x. List.mem x set && checkRoplist guard x.ropList*)

let rec trasverseRoMap releaseLabels roMap guard releasesFound= 
   match releaseLabels with 
   | [] -> releasesFound
   | x :: xs -> 
      try let set = IntMap.find x roMap in
      if checkGroupsLastRelease set guard then 
         trasverseRoMap xs roMap guard (releasesFound+1)
      else trasverseRoMap xs roMap guard releasesFound
    with Not_found -> (
      trasverseRoMap xs roMap guard releasesFound
    )
      (* @releasesFound = trasverseRoMap releaseLabels roMap guard releasesFound 
         *)
      
(*Função que filtra as labels para as labels superiores ou iguais à guarda
   e chama a função trasverseRoMap*)
let computeReleaseBindings label roMap guard=
   let bindings = IntMap.bindings roMap in 
   let labels = List.map (fun (k, _) -> k) bindings in
   let releaseLabels = List.filter ( fun x -> x >= label ) labels in 
   let (releasesFound:int) = trasverseRoMap releaseLabels roMap guard 0 in
   if releasesFound = 1 then 
      true
   else false

let checkLastRead (roMap:ResourceGroup.resourceGroup list IntMap.t) guard (guardRAccess:Access.resourceAccess)= 
            let guardLastRead = guardRAccess.Access.lastRead in 
            let guardLastWrite = guardRAccess.Access.lastWrite in 
            if guardLastRead < guardLastWrite then 
               computeReleaseBindings guardLastRead roMap guard
            else
               computeReleaseBindings guardLastWrite roMap guard
               
    (* @b = checkLastRead roMap firstWrite guard guardLastRead
      ensures true <-> (guardLastRead <= lastRead && 
          (let set = ResourceOperationsMap.find guardLastRead roMap in
          checkGroupsLastRead set guard = true))*)
let rec checkGroupsFirstOperation (set:ResourceGroup.resourceGroup list) guard op = 
   match set with 
   | [] -> false
   | x :: xs -> 
         
      let rec checkRopList guard (ropList:rOp list) op= 
         match ropList with
         | [] -> false
         | x :: xs ->
            if x.Roperation.r = guard && x.Roperation.op = op then 
               true
            else 
               checkRopList guard xs op in
                   (* @b = checkRopList guard ropList
                     requires guard >= -1
                     ensures true <-> (exists x. List.mem x ropList && x.op = 2)  *)
            
      if (checkRopList guard x.ResourceGroup.ropList op) then
         true
      else checkGroupsFirstOperation xs guard op
               (* @b = checkGroupsFirstRead set guard
                  requires guard >= -1
                  ensures true <-> exists x. List.mem x set && checkRoplist guard x.ropList*)
               
   let checkLastWrite (roMap:ResourceGroup.resourceGroup list IntMap.t) guard (guardRAccess:Access.resourceAccess)= 
      let guardLastWrite = guardRAccess.Access.lastWrite in 
      computeReleaseBindings guardLastWrite roMap guard
      
   let checkFirstWrite roMap firstWrite guard guardFirstWrite = 
      try if guardFirstWrite < firstWrite then 
      let set = IntMap.find guardFirstWrite roMap in
         if checkGroupsFirstOperation set guard 4 then 
            true
         else false
      else  false
      with Not_found -> (
      false
    )
      (* @b = checkFirstWrite roMap firstWrite guard guardFirstWrite
      ensures true <-> (guardFirstWrite <= firstWrite && 
          (let set = ResourceOperationsMap.find guardFirstWrite roMap in
          checkGroupsFirstWrite set guard = true))*)
      

let checkFirstRead (roMap:ResourceGroup.resourceGroup list IntMap.t) guard (guardRAccess:Access.resourceAccess)= 
         let guardFirstRead = guardRAccess.Access.firstRead in 
         let guardFirstWrite = guardRAccess.Access.firstWrite in 
          if guardFirstRead > guardFirstWrite then 
            try let setRead = IntMap.find guardFirstRead roMap in
            checkGroupsFirstOperation setRead guard 2
            with Not_found -> ( false )
         else
            try let setWrite = IntMap.find guardFirstWrite roMap in
            checkGroupsFirstOperation setWrite guard 4
         with Not_found -> ( false)
      (* @b = checkFirstRead roMap firstRead guard guardFirstWrite
      ensures true <-> (guardFirstWrite <= firstRead && 
          (let set = ResourceOperationsMap.find guardFirstWrite roMap in
          checkGroupsFirstRead set guard = true))*)
   

let readCheck guard roMap (guardRAccess:Access.resourceAccess)=
   if checkFirstRead roMap guard guardRAccess then 
      checkLastRead roMap guard guardRAccess
   else false
   (* @b = readCheck rAccess guard roMap guardRAccess
      requires guard >= -1   
   *)

let writeCheck (rAccess:Access.resourceAccess) guard roMap (guardRAccess:Access.resourceAccess) = 
   let firstWrite = rAccess.Access.firstWrite in 
   let guardFirstWrite = guardRAccess.Access.firstWrite in 
   if checkFirstWrite roMap firstWrite guard guardFirstWrite then 
      checkLastWrite roMap guard guardRAccess
   else false
   (* @b = writeCheck rAccess guard roMap guardRAccess
      requires guard >= -1   
   *)
let differentGuard label raMap (res:bool) guard roMap =
         let result = ref res in 
         try let rAccess = IntMap.find label raMap in 
         let guardRAccess = IntMap.find guard raMap in 
         let (firstWrite:int) = rAccess.Access.firstWrite in 
         let firstRead = rAccess.Access.firstRead in 
         if firstRead <> -1 then 
            result := readCheck guard roMap guardRAccess
         else ();
         if firstWrite <> -1 then 
            result := writeCheck rAccess guard roMap guardRAccess
         else ();
         !result 
        with Not_found ->(
          !result
        )
         (* @b = differentGuard label raMap result guard roMap*)

(*Função que  *)
let rec trasverseResources bindings (resourceMap:ResourceClass.resource IntMap.t) 
 (raMap:Access.resourceAccess IntMap.t) reslt roMap=
   match bindings with 
   | [] -> reslt
   | x :: xs ->
      try let res = IntMap.find x resourceMap in 
      let guard = res.ResourceClass.guardedBy in 
      if guard <> x then 
         begin
         let result = differentGuard x raMap reslt guard roMap in 
         if result then 
            trasverseResources xs resourceMap raMap result roMap
         else false
         end
      else 
         trasverseResources xs resourceMap raMap reslt roMap
      with Not_found -> (
        trasverseResources xs resourceMap raMap reslt roMap
      )
       (* @b = trasverseResources bindings resourceMap raMap result roMap*)


let lockGeneration (roMap:ResourceGroup.resourceGroup list IntMap.t) resourceMap raMap=
   let bindings = IntMap.bindings raMap in 
   let bindings = List.map (fun (k, _) -> k) bindings in 
   trasverseResources bindings resourceMap raMap true roMap


(* roMap
   0 
   1 res100 WRITE 
   2 res200 WRITE
   3 res200 RELEASE
   4 res300 READ
   5
   6 res100 RELEASE
   7 res300 RELEASE
   8 *)

   (* resourceMap
      100 -> res100 -> res100.guard = 100 
      200 -> res200 -> res200.guard = 100 
      300 -> res300 -> res300.guard = 300
   *)

   (* res100 -> 300
      res200 -> 300
      res300 -> 300
   *)

    (* Para o recurso 100, recorrer ao roMap e observar que, sendo a guarda
       deste o 300, todas as operações realizadas por este recurso
       estão contidas nas operações do 300*)
    
    (* Tem que se garantir que tanto antes/depois como dentro do recurso100
      as operações coincidem com os locks *)

    (* conjunto de testes para cada função*)

   (* lockMap1
      res100 -> lock100
      res200 -> lock200
      res300 -> lock100
   *)