open Resource
open ResourceGroup
open Mapping

(* Função semelhante à de baixo mas recebe um resourceGroup*)
let insertR label (rGroup:ResourceGroup.resourceGroup) rOperationsMap=
  let newROperationsMap = ref rOperationsMap in
  if IntMap.mem label rOperationsMap
    then () else
      begin
      let list = ref [] in
      newROperationsMap := IntMap.add label !list rOperationsMap;
      end;
  let list = ref [] in
  try list := IntMap.find label !newROperationsMap;
  list := !list @ [rGroup];
  let newROperationsMap = IntMap.add label !list !newROperationsMap in
  newROperationsMap

    with Not_found -> (
      rOperationsMap
    )

(* Função que recebe uma label e uma resourceOperation e cria um resource group adicionando-o à lista de resource groups*)

let createNewRGroup label rOperationsMap counter rop list= 
  let rGroup = ResourceGroup.rGroupVar() in
  let newRGroup = { id = counter; ropList = rGroup.ropList} in
  let newRGroup = ResourceGroup.add rop newRGroup in
  let newlist = list @ [newRGroup] in
  let newROperationsMap = IntMap.add label newlist rOperationsMap in
  newROperationsMap
(*@newROperationsMap = createNewRGroup label rOperationsMap counter rop list
  ensures exists newList.
    (newList = newROperationsMap.IntMap.view label && IntMap.mem label newROperationsMap) ->
    List.length list < List.length newList && 
    exists newRGroup.
    let rGroup = ResourceGroup.rGroupVar() in
    newRGroup = { id = counter; ropList = rGroup.ropList} &&
    List.mem newRGroup newList
*)

(* requires label => -1
   ensures result.view label = list*)
let insert (label:int) (rop:Roperation.rOp) rOperationsMap counter=
  try let list = IntMap.find label rOperationsMap in
    createNewRGroup label rOperationsMap counter rop list
  with Not_found ->(
    let list = [] in
    createNewRGroup label rOperationsMap counter rop list

)
  (*@newROperationsMap = insert label rop rOperationsMap counter
    ensures if IntMap.mem label rOperationsMap then 
     exists list newList.
      list = rOperationsMap.IntMap.view label &&
      (newList = newROperationsMap.IntMap.view label && IntMap.mem label newROperationsMap) ->
      List.length list < List.length newList && 
      exists newRGroup.
      let rGroup = ResourceGroup.rGroupVar() in
      newRGroup = { id = counter; ropList = rGroup.ropList} &&
      List.mem newRGroup newList
      else 
      exists newList.
      (newList = newROperationsMap.IntMap.view label && IntMap.mem label newROperationsMap) ->
       List.length newList > 0 && 
        exists newRGroup.
        let rGroup = ResourceGroup.rGroupVar() in
        newRGroup = { id = counter; ropList = rGroup.ropList} &&
        List.mem newRGroup newList
      *)

open Roperation

  let [@logic] insertRO opCode label res rOperationsMap counter=
    let (ro:Roperation.rOp)= {op = opCode; r = res} in
    insert label ro rOperationsMap counter
    (*@newROperationsMap = insertRO opCode label res rOperationsMap counter
       ensures let rop = {op = opCode; r = res} in
       if IntMap.mem label rOperationsMap then 
     exists list newList.
      list = rOperationsMap.IntMap.view label &&
      (newList = newROperationsMap.IntMap.view label && IntMap.mem label newROperationsMap) ->
      List.length list < List.length newList && 
      exists newRGroup.
      let rGroup = ResourceGroup.rGroupVar() in
      newRGroup = { id = counter; ropList = rGroup.ropList} &&
      List.mem newRGroup newList
      else 
      exists newList.
      (newList = newROperationsMap.IntMap.view label && IntMap.mem label newROperationsMap) ->
       List.length newList > 0 && 
        exists newRGroup.
        let rGroup = ResourceGroup.rGroupVar() in
        newRGroup = { id = counter; ropList = rGroup.ropList} &&
        List.mem newRGroup newList
    *)

(* Função que dado um recurso e as suas labels, cria uma resourceOperation de acordo com as condições e chama a função de insert*)
(*Pre: res >= 0
  Pre: access.firstWrite, access.firstRead etc. >= -1
  Pos: devolver o resourceOperations map correto dado as condições e os valores das labels
  *)
        
  let noReadLocks firstRead lastRead res rOperationsMap counter= 
    let rOperationsMap =insertRO 2 firstRead res rOperationsMap counter in 
    let counter = counter +1 in
    let rOperationsMap = insertRO 7 lastRead res rOperationsMap counter in 
    let counter = counter +1 in
    rOperationsMap, counter
    (*@newROperationsMap, newCounter = noReadLocks firstRead lastRead res rOperationsMap counter
      ensures  newCounter = counter + 2 
      ensures let rOperationsMap =insertRO 2 firstRead res rOperationsMap counter in 
              let counter = counter +1 in
              newROperationsMap = insertRO 7 lastRead res rOperationsMap counter
    *)

    let [@logic] firstReadORlastWrite firstRead lastWrite res rOperationsMap counter= 
      if firstRead < lastWrite then
        let newROperationsMap = insertRO 6 lastWrite res rOperationsMap counter in
        let newCounter = counter +1 in 
        newROperationsMap, newCounter
      else
        let newROperationsMap = insertRO 6 lastWrite res  rOperationsMap counter in
        let newCounter = counter +1 in 
        newROperationsMap, newCounter
    (*@newROperationsMap, newCounter = firstReadORlastWrite firstRead lastWrite res rOperationsMap counter
       ensures if firstRead < lastWrite then
        newROperationsMap = insertRO 6 lastWrite res rOperationsMap counter &&
        newCounter = counter +1 
      else
        newROperationsMap = insertRO 6 lastWrite res  rOperationsMap counter &&
        newCounter = counter +1
                *)
      

    let labelsVerification firstRead lastRead lastWrite res rOperationsMap counter=
      if firstRead == -1 || lastRead < lastWrite  then
        let newROperationsMap = insertRO 7 lastWrite res rOperationsMap counter in
        let newCounter = counter +1 in
        newROperationsMap, newCounter
      else 
        if lastWrite < lastRead then
          let newROperationsMap, newCounter = firstReadORlastWrite firstRead lastWrite res rOperationsMap counter in
          let newROperationsMap =insertRO 7 lastRead res newROperationsMap newCounter in
          let newCounter = newCounter +1 in
          newROperationsMap, newCounter
        else rOperationsMap, counter 
      (*@newROperationsMap, newCounter = labelsVerification firstRead lastRead lastWrite res rOperationsMap counter
          ensures if firstRead = -1 || lastRead < lastWrite  then
              newROperationsMap = insertRO 7 lastWrite res rOperationsMap counter &&
              newCounter = counter +1         
           else if lastWrite < lastRead then
              let newROperationsMap, newCounter = firstReadORlastWrite firstRead lastWrite res rOperationsMap counter in
              newROperationsMap =insertRO 7 lastRead res newROperationsMap newCounter &&
              newCounter = newCounter +1 
          else newROperationsMap = rOperationsMap && newCounter = counter 
      *)
      

    let firstWriteBefore firstRead firstWrite lastRead lastWrite res rOperationsMap counter = 
        let newROperationsMap = insertRO 4 firstWrite res rOperationsMap counter in
        let newCounter = counter +1 in
        labelsVerification firstRead lastRead lastWrite res newROperationsMap newCounter
        (*@newROperationsMap, newCounter = firstWriteBefore firstRead firstWrite lastRead lastWrite res rOperationsMap counter 
            ensures newCounter > counter
            ensures IntMap.mem firstWrite newROperationsMap && 
            if firstRead = -1 || lastRead < lastWrite  then
              IntMap.mem lastWrite newROperationsMap
            else 
              if lastWrite < lastRead then
                IntMap.mem lastWrite newROperationsMap && IntMap.mem lastRead newROperationsMap
              else IntMap.mem firstWrite newROperationsMap
        *)

    let firstReadBefore firstRead lastRead firstWrite lastWrite res counter rOperationsMap= 
    let newCounter = ref counter in
    let newROperationsMap = ref rOperationsMap in
    newROperationsMap := insertRO 3 firstRead res !newROperationsMap !newCounter;
    newCounter:= !newCounter +1;
    newROperationsMap :=insertRO 5 firstWrite res !newROperationsMap !newCounter;
    newCounter:= !newCounter +1;
    if lastRead < firstWrite then
      begin
        newROperationsMap :=insertRO 7 lastWrite res !newROperationsMap !newCounter;
        newCounter:= !newCounter +1;
      end
    else if lastRead < lastWrite then
      begin
        newROperationsMap :=insertRO 6 lastWrite res !newROperationsMap !newCounter;
        newCounter:= !newCounter +1;
        newROperationsMap :=insertRO 7 lastRead res !newROperationsMap !newCounter;
        newCounter:= !newCounter +1;
      end
    else ();
    !newROperationsMap, !newCounter
      (*@newROperationsMap, newCounter = firstReadBefore firstRead lastRead firstWrite lastWrite res counter rOperationsMap
        ensures newCounter > counter
        ensures IntMap.mem firstRead newROperationsMap && IntMap.mem firstWrite newROperationsMap &&
          if lastRead < firstWrite then
            IntMap.mem lastWrite newROperationsMap
          else if lastRead < lastWrite then
            IntMap.mem lastWrite newROperationsMap &&
            IntMap.mem lastRead newROperationsMap
          else IntMap.mem firstRead newROperationsMap && IntMap.mem firstWrite newROperationsMap
      
      *)


let computeROperations res (access: Access.resourceAccess) rOperationsMap counter=
  (*if the resource isn't read or written on the method, no locks are required*)
    let firstWrite = access.Access.lastWrite in
    let firstRead = access.Access.firstRead in
    let lastWrite = access.Access.lastWrite in
    let lastRead = access.Access.lastRead in
    let accessible_from = access.Access.first in
    let counter = ref counter in
    let rOperationsMap = ref rOperationsMap in
    if firstWrite != -1 || firstRead != -1  then
      begin
      rOperationsMap := insertRO 1 accessible_from res !rOperationsMap !counter;
      counter:= !counter +1;
      (*if it isn't written, then only read locks are required*)
      if firstWrite == -1 then
        begin
        let a,b = noReadLocks firstRead lastRead res !rOperationsMap !counter in
        rOperationsMap := a;
        counter := b;
        end
      (*it either isn't read or firstWrite < firstRead*)
      else if firstRead == -1 || firstWrite < firstRead then
        begin
        let a,b = firstWriteBefore firstRead firstWrite lastRead lastWrite res !rOperationsMap !counter in 
        rOperationsMap := a;
        counter := b;
        end
        else if firstRead < firstWrite then
          begin
          let a,b = firstReadBefore firstRead lastRead firstWrite lastWrite res !counter !rOperationsMap in
          rOperationsMap := a;
          counter := b;
          end
          else ()
        end
      else ();
    !rOperationsMap, !counter

open Mapping

(* Função recursiva: Recebe um mapa e as suas chaves como argumento e vai extrair o valor de cada chamando depois
   a função computeROperations para este par de chave,valor*)
(*Pre: receber as chaves todas do raMap bem como o rOperations vazio
  Pos: devolver o rOperations alterado quando todas as chaves tiverem sido percorridas*)
let rec getPair accessMap bindings rOperationsMap counter=
  match bindings with
  | [] -> rOperationsMap
  | x :: xs -> (
    try let access: Access.resourceAccess = IntMap.find x accessMap in
    let rOperationsMap, counter = computeROperations x access rOperationsMap counter in
    getPair accessMap xs rOperationsMap counter
    with Not_found -> (
      getPair accessMap xs rOperationsMap counter
    ))
    (* @result = getPair accessMap bindings rOperationsMap*)

(* Função recursiva: Percorre as chaves do mapa recebidas como argumento e extrai o seu value*)
(* O seu value é um mapa que mapeia resources (ints) -> resourceAccess*)
(* Por fim ela chama a função getPair para cada chave*)
(*Pre : receber o raMap bem construido
  Pos : devolver o mapa dos resourceOperations bem construido relativos a este raMap*)
let computeBindings (raMap:Resource.Access.resourceAccess Mapping.IntMap.t)=
  (*print_string "rOperations Map Generation compute Bindings \n";*)
  let bindingsAccess = Mapping.IntMap.bindings raMap in
  let bindingsAccess = List.map (fun (k, _) -> k) bindingsAccess in
  let rOperationsMap = IntMap.empty in
  let counter = 0 in
  let newROperationsMap = getPair raMap bindingsAccess rOperationsMap counter in
  newROperationsMap
