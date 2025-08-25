 module ResourceClass =
  struct
  (*
  type whatIs =
  | 0 (* field*)
  | 1 (* methodCall*)
  | 2 (* cast*)
  | 3 (* object*)
  | 4 (* error*)
  *)
  type resource = {
    position: int;
    ty: int;
    vis: int;
    nature: bool;
    whatIs: int;
    guardedBy : int;
    isParameter : bool
  }
  
  let make_resource pos ty vis nature whatIs guardedBy isParameter = 
    {position = pos; ty = ty; vis = vis; nature = nature; whatIs = whatIs; 
    guardedBy = guardedBy; isParameter = isParameter } 

    let resourceVar () = {position=0; ty = 0; vis = 0; nature = true; whatIs = 0; guardedBy = -1; isParameter = false}
    
  
    let [@logic] setIsParameter res isParameter = 
      let newRes = { position = res.position; ty = res.ty; vis = res.vis;
      whatIs = res.whatIs; nature = res.nature; guardedBy = res.guardedBy; isParameter = isParameter} in 
      newRes
      (*@ r = setIsParameter res isParameter
         ensures r.isParameter = isParameter*)


    let [@logic] isField w =
      if w = 0 then true else false
    (*@ b = isField w
       ensures b -> w = 0*)
  
    let isCast w =
      if w = 1 then true else false
       (*@ b = isCast w
       ensures b -> w = 1*)
  
    let isMethodcall w =
      if w = 2 then true else false
    (*@ b = isMethodcall w
       ensures b -> w = 2*)
  
    let isObject w =
      if w = 3 then true else false
     (*@ b = isObject w
       ensures b -> w = 3*)
  
  
    let setGuard guard res= 
    let newRes = { position = res.position; ty = res.ty; vis = res.vis;
    whatIs = res.whatIs; nature = res.nature; guardedBy = guard; isParameter = res.isParameter} in 
    newRes
    (*@ r = setGuard guard res
       ensures r.guardedBy = guard*)
  
  
  
  end;;
  
  module Access =
  struct
(*The type of resourceAccesses*)
  type resourceAccess = { 
                  first : int;
                  firstRead : int;
                  lastRead :int;
                  firstWrite : int;
                  lastWrite :int
  }

  let rAccess () :resourceAccess= {
    first = -1;
    firstRead = -1;
    lastRead = -1;
    firstWrite = -1;
    lastWrite = -1
  }
  (*@ ra = rAccess ()
      ensures ra.first = -1
      ensures ra.firstRead = -1
      ensures ra.lastRead = -1
      ensures ra .firstWrite = -1
      ensures ra.lastWrite = -1*)


  let [@logic ] hasReadAccess rA= 
   rA.firstRead <> -1
   (*@ b = hasReadAccess rA
      ensures b -> rA.firstRead <> -1
    *)
  
  let [@logic ] hasWriteAccess rA= 
    rA.firstWrite <> -1
    (*@ b = hasWriteAccess rA
      ensures b -> rA.firstWrite <> -1
    *)

  let [@logic ] resourceAccessCons (l: int list) =
    let lfirst, lfirstRead, llastRead, lfirstWrite, llastWrite = 
      match l with
      | [lfirst; lfirstRead; llastRead; lfirstWrite; llastWrite] -> lfirst, lfirstRead, llastRead, lfirstWrite, llastWrite
      | _ -> assert false in
      { first = lfirst; firstRead = lfirstRead; lastRead = llastRead; firstWrite = lfirstWrite; lastWrite = llastWrite} 
    
    (*@ ra = resourceAccessCons l
        requires List.length l = 5
        ensures
        match l with
          | (lfirst :: (lfirstRead :: (llastRead :: (lfirstWrite :: (llastWrite :: []))))) -> 
          ra.first = lfirst 
          && ra.firstRead = lfirstRead 
          && ra.lastRead = llastRead 
          && ra.firstWrite = lfirstWrite 
          && ra.lastWrite = llastWrite
          && lfirstRead = -1 -> not (hasReadAccess ra)
          && lfirstWrite = -1 -> not (hasWriteAccess ra)
          |_ -> false
    *)
  
  let replaceFirstWrite label rA= 
    {first = rA.first; firstRead = rA.firstRead; lastRead = rA.lastRead; firstWrite = label; lastWrite = rA.lastWrite}
    (*@ ra = replaceFirstWrite label rA
        requires label > -2
        ensures ra.firstWrite = label   
    *)
  
  let replaceLastWrite label rA=
  {first = rA.first; firstRead = rA.firstRead; lastRead = rA.lastRead; firstWrite = rA.firstWrite; lastWrite = label}
  (*@ ra = replaceLastWrite label rA
      requires label > -2
      ensures ra.lastWrite = label   
  
  *)

  (* Function that returns the smallest int between firstRead and firstWrite*)
  let getFirst rA = 
    let fr = rA.firstRead in 
    let fw = rA.firstWrite in 
    if fw < fr then fw else fr
    (*@ res = getFirst rA
       requires rA.firstRead <> rA.firstWrite
       requires rA.firstRead > -2 && rA.firstWrite > -2 && (rA.firstRead > -1 || rA.firstWrite > -1)
       ensures res = rA.firstWrite -> (rA.firstWrite < rA.firstRead)
       ensures res = rA.firstRead -> (rA.firstWrite > rA.firstRead) *)

  (* Function that returns the biggest int between firstRead and firstWrite*)
  let getLast rA = 
      let lr = rA.lastRead in 
      let lw = rA.lastWrite in 
      if lr > lw then lr else lw
    (*@ res = getLast rA
        requires rA.lastRead <> rA.lastWrite
        requires rA.lastRead > -2 && rA.lastWrite > -2 && (rA.lastRead > -1 || rA.lastWrite > -1)
        ensures res = rA.lastRead -> rA.lastRead > rA.lastWrite
        ensures res = rA.lastWrite -> rA.lastRead < rA.lastWrite *)
    
  end

(*type opCode =
| EMPTY 0
| AVAILABLE 1
| READ 2
| SHARED_BEFORE_EXCLUSIVE 3
| WRITE 4
| UPGRADE 5
| DOWNGRADE 6
| RELEASE 7*)

type rOp = { op : int; 
             r: int;
}

  module IntMap = Map.Make(Int)

  module ClassMethodInfoMap = Map.Make(String)


      let [@logic] firstElement list =
        match list with
           | [] -> (assert false)
           | x::_ -> x
        (*@r = firstElement list
          requires list <> []  
          ensures match list with
           | [] -> false
           | x::_ -> r = x*)


(*
  let rec print_list = function 
    [] -> ()
    | e::l -> print_string " Print do split: "; print_string e ; print_string " " ; print_list l 
*)
  let [@logic] append_item lst a = 
    lst @ [a]
    (*@ newList = append_item lst a
       ensures List.length newList > List.length lst && 
       List.mem a newList *)

  let computeResourceMethodsMap res classAndMethod resourceMethodsMap=
    try let methodArray = IntMap.find res resourceMethodsMap in 
     let newMethodArray = append_item methodArray classAndMethod in
     let newResourceMethodsMap = IntMap.add res newMethodArray resourceMethodsMap in
     newResourceMethodsMap
     with Not_found -> (
       resourceMethodsMap
     )
      (*@ newResourceMethodsMap = computeResourceMap res classAndMethod resourceMethodsMap
      ensures if IntMap.mem res resourceMethodsMap then 
          exists methodArray.
          methodArray = newResourceMethodsMap.IntMap.view res && 
          List.mem classAndMethod methodArray
        else
          IntMap.mem res newResourceMethodsMap = false 
  *)

    let isResourceParameter resourceMap resId = 
      try let resource = IntMap.find resId resourceMap in
      let newResource = ResourceClass.setIsParameter resource true in
      let newResourceMap = IntMap.add resId newResource resourceMap in 
      newResourceMap
      with Not_found -> (
        resourceMap
      )
      (*@newResourceMap = isResourceParameter resourceMap resId
         ensures exists newResource.
          if IntMap.mem resId resourceMap then 
          newResource = newResourceMap.IntMap.view resId && IntMap.mem resId newResourceMap &&
          newResource.ResourceClass.isParameter
          else
          IntMap.mem resId newResourceMap = false*)


          let [@logic] tryRes (raMap:Access.resourceAccess IntMap.t) resId listLabels resourceMap =
          let newResourceMap = ref resourceMap in
          let accessible_from = firstElement listLabels in
          if accessible_from = -1 then
            let isParam = isResourceParameter resourceMap resId in
            newResourceMap := isParam;
            let rAccess = Access.resourceAccessCons listLabels in
            let newRaMap = IntMap.add resId rAccess raMap in
            newRaMap, !newResourceMap
          else
            let rAccess = Access.resourceAccessCons listLabels in
            let newRaMap = IntMap.add resId rAccess raMap in
            newRaMap, !newResourceMap
        (*@newRaMap, newResourceMap = tryRes raMap resId listLabels resourceMap
          requires listLabels <> []
          requires List.length listLabels = 5
          requires resId >= 0
          ensures let accessible_from = firstElement listLabels in
              accessible_from = -1 -> 
              exists newResource.
              if IntMap.mem resId resourceMap then 
              newResource = newResourceMap.IntMap.view resId && IntMap.mem resId newResourceMap &&
              newResource.ResourceClass.isParameter
              else
              IntMap.mem resId newResourceMap = false
          ensures exists rAccess.
                rAccess = Access.resourceAccessCons listLabels &&
                rAccess = newRaMap.IntMap.view resId
        *)

        
        let classNotFound res classAndMethod listLabels classInfoMap resourceMethodsMap resourceMap =
          let raMap, newResourceMap = tryRes IntMap.empty res listLabels resourceMap in
          let classInfoMap = ClassMethodInfoMap.add classAndMethod raMap classInfoMap in
          let newResourceMethodsMap = computeResourceMethodsMap res classAndMethod resourceMethodsMap in
          classInfoMap, newResourceMap, newResourceMethodsMap
          (*@ newClassMap, newResourceMap, newResourceMethodsMap = classNotFound res classAndMethod listLabels classInfoMap resourceMethodsMap resourceMap
               requires listLabels <> []
               requires List.length listLabels = 5
               requires res >= 0
               ensures  ClassMethodInfoMap.mem classAndMethod newClassMap &&
                        newClassMap.ClassMethodInfoMap.view classAndMethod  = fst (tryRes IntMap.empty res listLabels resourceMap) &&
                        (if IntMap.mem res resourceMethodsMap then 
                           let methodArray = newResourceMethodsMap.IntMap.view res  in
                           List.mem classAndMethod methodArray
                         else
                           not (IntMap.mem res newResourceMethodsMap))*)
          
        

  (* Função que recebe informação sobre a classe, metodo etc. E cria ou adiciona esta informação para o mapa classMethodInfo
    Caso esta class/metodo não exista ainda, então esta chama a função classNotFound*)
    let computeLine listLabels classAndMethod res (classMethodInfoMap:Access.resourceAccess IntMap.t ClassMethodInfoMap.t)
    (resourceMap:ResourceClass.resource IntMap.t) (resourceMethodsMap:string list IntMap.t)=
    try let (raMap:Access.resourceAccess IntMap.t)  = ClassMethodInfoMap.find classAndMethod classMethodInfoMap in
     let a,b = tryRes raMap res listLabels resourceMap in
      let rAccessHashMap = a in
      let newResourceMap = b in
      let (newClassMethodInfoMap:Access.resourceAccess IntMap.t ClassMethodInfoMap.t) = ClassMethodInfoMap.add classAndMethod rAccessHashMap classMethodInfoMap in
      let newResourceMethodsMap = computeResourceMethodsMap res classAndMethod resourceMethodsMap in
      newClassMethodInfoMap, newResourceMap, newResourceMethodsMap
    with Not_found -> (
      let newClassMethodInfoMap, newResourceMap, newResourceMethodsMap = classNotFound res classAndMethod listLabels classMethodInfoMap resourceMethodsMap resourceMap in
      newClassMethodInfoMap, newResourceMap, newResourceMethodsMap)
    (*@newClassMethodInfoMap, newResourceMap, newResourceMethodsMap = computeLine listLabels classAndMethod res classMethodInfoMap resourceMap resourceMethodsMap
      requires listLabels <> []
      requires List.length listLabels = 5 
      requires res >= 0
      ensures if ClassMethodInfoMap.mem classAndMethod classMethodInfoMap then 
        let raMap =  classMethodInfoMap.ClassMethodInfoMap.view classAndMethod in
        let a,b = tryRes raMap res listLabels resourceMap in
        ClassMethodInfoMap.mem classAndMethod newClassMethodInfoMap && 
        newClassMethodInfoMap.ClassMethodInfoMap.view classAndMethod = a && 
        newResourceMap = b &&
        if IntMap.mem res resourceMethodsMap then 
          exists methodArray.
          methodArray = newResourceMethodsMap.IntMap.view res && 
          List.mem classAndMethod methodArray
        else
          IntMap.mem res newResourceMethodsMap = false 
      else
        let raMap = IntMap.empty in
      let raMap,resourceMap = tryRes raMap res listLabels resourceMap in
      (ClassMethodInfoMap.mem classAndMethod newClassMethodInfoMap && newClassMethodInfoMap.ClassMethodInfoMap.view classAndMethod = raMap) &&
     if IntMap.mem res resourceMethodsMap then 
          exists methodArray.
          methodArray = newResourceMethodsMap.IntMap.view res && 
          List.mem classAndMethod methodArray
        else
          IntMap.mem res newResourceMethodsMap = false 
        *)


  (* Função que recebe a informação necessário sobre um recurso e depoois de cria-lo, ele é inserido no mapa de recursos*)
  let computeResource resId typ visib nature whatIs resourceMap resourceMethodsMap=
    let (r:ResourceClass.resource) = {ResourceClass.position = resId; ResourceClass.ty = typ; ResourceClass.vis = visib;
    ResourceClass.nature = nature; ResourceClass.whatIs =  whatIs; 
    ResourceClass.guardedBy = resId; ResourceClass.isParameter = false} in
    let newResourceMap = IntMap.add resId r resourceMap in 
    let newResourceMethodsMap = IntMap.add resId [] resourceMethodsMap in 
    newResourceMap, newResourceMethodsMap
    (*@newResourceMap, newResourceMethodsMap = computeResource resId typ visib nature whatIs resourceMap resourceMethodsMap
      requires resId >= 0
      ensures  let (r:ResourceClass.resource) = 
      {ResourceClass.position = resId; ResourceClass.ty = typ; ResourceClass.vis = visib;
      ResourceClass.nature = nature; ResourceClass.whatIs =  whatIs; 
      ResourceClass.guardedBy = resId; ResourceClass.isParameter = false} in
      (IntMap.mem resId newResourceMap && newResourceMap.IntMap.view resId = r) && 
      (IntMap.mem resId newResourceMethodsMap && newResourceMethodsMap.IntMap.view resId = [] ) 

      (* WRITE-LOCK GUARD: newly created resource is self-guarded *)
      ensures
        (newResourceMap.IntMap.view resId).ResourceClass.guardedBy = resId

      (* Frame: pre-existing entries are unchanged by creation *)
      ensures
        forall k. k <> resId && IntMap.mem k resourceMap ->
          IntMap.mem k newResourceMap &&
          newResourceMap.IntMap.view k = resourceMap.IntMap.view k
  *)

type resourceGroup = {
  id : int;
  ropList : rOp list
}

let roEqual ro1 =
  let ro2 = {op = 0; r = -1} in 
  ro1.op = ro2.op && ro1.r = ro2.r
(*@ b = roEqual ro1
    ensures b <-> (ro1.op = 0 && ro1.r = -1) *)

let [@logic] rGroupVar () = { id = -1; ropList = []}
(*@ rg = rGroupVar ()
    ensures rg.id = -1
    ensures rg.ropList = [] *)

let setId id resGroup =
  let newResGroup = { id = id ; ropList = resGroup.ropList} in  
  newResGroup
  (*@ rg = setId id resGroup
    ensures rg.id = id
    ensures rg.ropList = resGroup.ropList *)

let add (rOp: rOp) resGroup = 
  let newResGroup = { id = resGroup.id ; ropList = resGroup.ropList @ [rOp]} in  newResGroup
  (*@rg = add rop resGroup
     ensures List.mem rop rg.ropList*)

  
  
let [@logic] rec getResult ropList (rop:rOp) =
  match ropList with
  | [] -> false
  | ropX::ropXS -> (
    if rop.r = ropX.r && rop.op = ropX.op  then true 
    else getResult ropXS rop
  )
      (*@b = getResult ropList ropaux
         variant ropList
         ensures b = true <-> List.mem ropaux ropList 
        *)


  let [@logic] diff rop1 rop2= 
  (rop1.r <> rop2.r || rop1.op <> rop2.op)
  (*@ b = diff rop1 rop2
    ensures b <-> not (rop1.r = rop2.r && rop1.op = rop2.op) *)

  let [@logic] remove (rOp: rOp) resGroup = 
    let newRopList = List.filter (diff rOp) resGroup.ropList in
    { id = resGroup.id; ropList = newRopList}
    (*@ rg = remove3 rOp resGroup
        ensures List.mem rOp rg.ropList = false*)
      

(* Compara duas listas e determina se uma está contida na outra*)
let[@logic] rec sub (l:string list) (ll:string list) = 
  match (l,ll) with
  | [],_ -> false
  | _,[] -> true
  | (h::t), (hh::tt) -> (if h == hh then sub t tt
                        else sub t ll )
(*@b = sub l1 l2
   variant l1
   variant l2
   ensures b = true -> forall x. List.mem x l2 -> List.mem x l1 
   *)
   
(*Função que verifica se um recurso é dominado pelo o outro num certo método
   Retorna verdadeiro se for e falso se não*)
   let dominatesCheck (dominantAccess:Access.resourceAccess) (r2Access:Access.resourceAccess)=
   let res = ref true in
   if r2Access.Access.firstRead <> -1 then
     begin
       if (dominantAccess.Access.firstRead > r2Access.Access.firstRead 
         && (dominantAccess.Access.firstRead > r2Access.Access.firstWrite || 
          r2Access.Access.firstWrite = -1))
         || (dominantAccess.Access.lastRead < r2Access.Access.lastRead 
         && (dominantAccess.Access.lastRead < r2Access.Access.lastWrite || 
          r2Access.Access.lastWrite = -1))
          then 
           res := false
          
         else ()
       end
     else ();
   
     if  r2Access.Access.firstWrite <> -1 then 
       begin
       if dominantAccess.Access.firstWrite > r2Access.Access.firstWrite 
         || dominantAccess.Access.lastWrite < r2Access.Access.lastWrite then
         res := false
       else ()
     end
   else ();
   !res
   (*@res = dominatesCheck dA rA
      ensures res = false <-> (rA.Access.firstRead <> -1  && (dA.Access.firstRead > rA.Access.firstRead 
       && (dA.Access.firstRead > rA.Access.firstWrite || rA.Access.firstWrite = -1 )|| dA.Access.lastRead < rA.Access.lastRead 
       && (dA.Access.lastRead < rA.Access.lastWrite || rA.Access.lastWrite = -1)) 
       || (rA.Access.firstWrite <> -1 && ( dA.Access.firstWrite > rA.Access.firstWrite 
       || dA.Access.lastWrite < rA.Access.lastWrite)))
        *)
    
  (*Função que altera a guarda do recurso a ser dominado e chama a função subsumedMethodsCycle. Rrtorna o novo ClassMethodInfoMap*)
  (*Função booleana que faz o find dos accesses dos recursos e chama a função de dominatesCheck para verificar se estes são dominados*)
  (* Pre: locked = false*)
  let dominates (r2Met: string) (res1:ResourceClass.resource) (res2:ResourceClass.resource) classMethodInfoMap= 
          try let raMap = ClassMethodInfoMap.find r2Met classMethodInfoMap in
          let r1Access = IntMap.find res1.ResourceClass.position raMap in
          let r2Access = IntMap.find res2.ResourceClass.position raMap in
          dominatesCheck r1Access r2Access
          with Not_found ->( 
            false
          )
      (*@res = dominates m r1 r2 cmInfoMap
      requires m <> ""
      ensures res -> exists raMap dA rA. 
        (raMap = cmInfoMap.ClassMethodInfoMap.view m && ClassMethodInfoMap.mem m cmInfoMap)  && 
        (dA = raMap.IntMap.view r1.ResourceClass.position && IntMap.mem r1.ResourceClass.position raMap)  &&
        (rA = raMap.IntMap.view r2.ResourceClass.position && IntMap.mem r2.ResourceClass.position raMap) &&
         (not (rA.Access.firstRead <> -1  && ( dA.Access.firstRead > rA.Access.firstRead 
           && dA.Access.firstRead > rA.Access.firstWrite ||dA.Access.lastRead < rA.Access.lastRead 
          && dA.Access.lastRead < rA.Access.lastWrite)) 
          || (rA.Access.firstWrite <> -1 && ( dA.Access.firstWrite > rA.Access.firstWrite 
          || dA.Access.lastWrite < rA.Access.lastWrite)))
          *)
    
  (* Função que percorre os metodos do recurso 2 (r2methods) e altera o resultado para falso caso não 
    encontre uma situação onde não existe dominancia. Retorna um booleano com o resultado *)
  let [@logic] rec methodCycle r2methods (res:bool ) resource1 resource2 classMethodInfoMap= 
    match r2methods with 
    | [] -> res
    | x :: xs -> 
      if res then 
        let newRes = dominates x resource1 resource2 classMethodInfoMap in
        methodCycle xs newRes resource1 resource2 classMethodInfoMap
      else 
        false
      (*@result = methodCycle r2methods res r1 r2 cmInfoMap
          requires forall m. List.mem m r2methods -> m <> ""
          variant r2methods
          ensures result -> res = true && 
            forall m. List.mem m r2methods -> 
            exists raMap dA rA.
            (raMap = cmInfoMap.ClassMethodInfoMap.view m && ClassMethodInfoMap.mem m cmInfoMap)  && 
            (dA = raMap.IntMap.view r1.ResourceClass.position && IntMap.mem r1.ResourceClass.position raMap)  &&
            (rA = raMap.IntMap.view r2.ResourceClass.position && IntMap.mem r2.ResourceClass.position raMap) &&
            (not (rA.Access.firstRead <> -1  && ( dA.Access.firstRead > rA.Access.firstRead 
            && dA.Access.firstRead > rA.Access.firstWrite ||dA.Access.lastRead < rA.Access.lastRead 
            && dA.Access.lastRead < rA.Access.lastWrite)) 
            || (rA.Access.firstWrite <> -1 && ( dA.Access.firstWrite > rA.Access.firstWrite 
            || dA.Access.lastWrite < rA.Access.lastWrite)))

          ensures result = false -> res = false ||
            exists m. List.mem m r2methods -> 
            exists raMap dA rA. 
            ((raMap = cmInfoMap.ClassMethodInfoMap.view m && ClassMethodInfoMap.mem m cmInfoMap)  && 
            (dA = raMap.IntMap.view r1.ResourceClass.position && IntMap.mem r1.ResourceClass.position raMap)  &&
            (rA = raMap.IntMap.view r2.ResourceClass.position && IntMap.mem r2.ResourceClass.position raMap) &&
            not (rA.Access.firstRead <> -1  && ( dA.Access.firstRead > rA.Access.firstRead 
            && dA.Access.firstRead > rA.Access.firstWrite ||dA.Access.lastRead < rA.Access.lastRead 
            && dA.Access.lastRead < rA.Access.lastWrite)) 
            || (rA.Access.firstWrite <> -1 && ( dA.Access.firstWrite > rA.Access.firstWrite 
            || dA.Access.lastWrite < rA.Access.lastWrite))) = false
                
           
      *)

  let resourceMapUpdate res resource1 resource2 resourceMap= 
    if res then
      begin
      let resSubsumed = ResourceClass.setGuard resource1.ResourceClass.position resource2 in
      let newResourceMap = IntMap.add resource2.ResourceClass.position resSubsumed resourceMap in 
      newResourceMap
      end
    else
      resourceMap
      (*@newResourceMap =  resourceMapUpdate res resource1 resource2 resourceMap
          ensures res = true -> 
          exists newResource2. 
          newResource2 = newResourceMap.IntMap.view resource2.ResourceClass.position &&
          IntMap.mem resource2.ResourceClass.position newResourceMap && 
          newResource2.ResourceClass.guardedBy = resource1.ResourceClass.position
          *)

  (* Se um array está contido noutro array então verifica se existe dominancia e se esta for verificada atualizamos o nosso mapa *)
  let logic resource1 resource2 res classMethodInfoMap resourceMethodsMap resourceMap= 
    try let r1methods = IntMap.find resource1.ResourceClass.position resourceMethodsMap in
        let r2methods = IntMap.find resource2.ResourceClass.position resourceMethodsMap in
        if sub r1methods r2methods then 
          res := methodCycle r2methods true resource1 resource2 classMethodInfoMap
        else ();
    resourceMapUpdate !res resource1 resource2 resourceMap
  with Not_found ->
    resourceMapUpdate !res resource1 resource2 resourceMap
    (*@newResourceMap = logic resource1 resource2 res classMethodInfoMap resourceMethodsMap resourceMap
      requires 
        forall keys. IntMap.mem keys resourceMethodsMap ->
          forall values. List.mem values (resourceMethodsMap.IntMap.view keys) ->
           values <> ""
      ensures exists r1methods r2methods. 
      (r1methods = resourceMethodsMap.IntMap.view resource1.ResourceClass.position && IntMap.mem resource1.ResourceClass.position resourceMethodsMap) &&
      (r2methods = resourceMethodsMap.IntMap.view resource2.ResourceClass.position && IntMap.mem resource2.ResourceClass.position resourceMethodsMap ) &&
      (sub r1methods r2methods && methodCycle r2methods true resource1 resource2 classMethodInfoMap ) ->
         exists newResource2. 
          newResource2 = newResourceMap.IntMap.view resource2.ResourceClass.position &&
          IntMap.mem resource2.ResourceClass.position newResourceMap && 
          newResource2.ResourceClass.guardedBy = resource1.ResourceClass.position          
    *)


  (* Função que encontra um segundo recurso para testar se existe dominancia 
     Começa por encontrar os metodos onde ambos os recursos estão presentes e verificar que uma das listas é uma sublista da outra
     Se isto se verificar chamamos a função methodCycle que vai atualizar a variavel res
     Se esta variavel for retornada como true, então existe dominancia e é chamada a função para fazer o subsume do recurso
  *)
  let [@logic] rec  findSndResource keys  (classMethodInfoMap:Access.resourceAccess IntMap.t ClassMethodInfoMap.t) 
  (resource1:ResourceClass.resource) resourceMap resourceMethodsMap= 
    match keys with 
    | [] -> resourceMap
    | x :: xs -> 
        let res = ref false in
        try let (resource2:ResourceClass.resource) = IntMap.find x resourceMap in
        if resource1.ResourceClass.position = x then 
          findSndResource xs classMethodInfoMap resource1 resourceMap resourceMethodsMap
        else
          let newResourceMap = logic resource1 resource2 res classMethodInfoMap resourceMethodsMap resourceMap in
          findSndResource xs classMethodInfoMap resource1 newResourceMap resourceMethodsMap
        with Not_found -> (
            findSndResource xs classMethodInfoMap resource1 resourceMap resourceMethodsMap
        )
    (*@result = findSndResource keys classMethodInfoMap resource1 resourceMap resourceMethodsMap        
      requires 
        forall keys2. IntMap.mem keys2 resourceMethodsMap ->
          forall values. List.mem values (resourceMethodsMap.IntMap.view keys2) ->
           values <> ""
      variant keys
      ensures forall res2Id. 
      List.mem res2Id keys -> 
        exists resource2.
      IntMap.mem res2Id resourceMap && resource2 = resourceMap.IntMap.view res2Id ->
      resource1.ResourceClass.position <> res2Id ->
        exists r1methods r2methods. 
      (r1methods = resourceMethodsMap.IntMap.view resource1.ResourceClass.position && IntMap.mem resource1.ResourceClass.position resourceMethodsMap) &&
      (r2methods = resourceMethodsMap.IntMap.view resource2.ResourceClass.position && IntMap.mem resource2.ResourceClass.position resourceMethodsMap ) &&
      (sub r1methods r2methods && methodCycle r2methods true resource1 resource2 classMethodInfoMap ) ->
         exists newResource2. 
          newResource2 = result.IntMap.view resource2.ResourceClass.position &&
          IntMap.mem resource2.ResourceClass.position result && 
          newResource2.ResourceClass.guardedBy = resource1.ResourceClass.position
        
    *)


(*Função que captura as bindins do mapa dos recursos *)
let [@logic] sndResource resourceMap resource1 resourceMethodsMap classMethodInfoMap= 
let bindings = IntMap.bindings resourceMap in
let keys = List.map (fun (k, _) -> k) bindings in
let newResourceMap =  findSndResource keys classMethodInfoMap resource1 resourceMap resourceMethodsMap in
newResourceMap
(*@result = sndResource resourceMap resource1 resourceMethodsMap classMethodInfoMap
  requires forall keys. IntMap.mem keys resourceMethodsMap ->
          forall values. List.mem values (resourceMethodsMap.IntMap.view keys) ->
           values <> ""
  ensures forall k. IntMap.mem k resourceMap-> 
    exists resource2.
      IntMap.mem k resourceMap && resource2 = resourceMap.IntMap.view k ->
      resource1.ResourceClass.position <> k ->
        exists r1methods r2methods. 
      (r1methods = resourceMethodsMap.IntMap.view resource1.ResourceClass.position && IntMap.mem resource1.ResourceClass.position resourceMethodsMap) &&
      (r2methods = resourceMethodsMap.IntMap.view resource2.ResourceClass.position && IntMap.mem resource2.ResourceClass.position resourceMethodsMap ) &&
      (sub r1methods r2methods && methodCycle r2methods true resource1 resource2 classMethodInfoMap ) ->
         exists newResource2. 
          newResource2 = result.IntMap.view resource2.ResourceClass.position &&
          IntMap.mem resource2.ResourceClass.position result && 
          newResource2.ResourceClass.guardedBy = resource1.ResourceClass.position

      
*)


(*Funçao que recebe todos os inteiros correspondentes aos recursos e os 3 mapas
  Processa as chaves uma a uma e se o recurso for um Field entao chama a função que processa o segundo recurso
  Recebe dessa função os 3 mapas alterados e retorna-os*)

let rec fstResource keys resourceMap resourceMethodsMap classMethodInfoMap=
  match keys with
  | [] -> resourceMap
  | x :: xs -> (
  try let res:ResourceClass.resource = IntMap.find x resourceMap in
  let whatIs = res.ResourceClass.whatIs in
  let isField = ResourceClass.isField whatIs in
  if isField && res.ResourceClass.nature then 
    let newResourceMap = sndResource resourceMap res resourceMethodsMap classMethodInfoMap in 
    fstResource xs newResourceMap resourceMethodsMap classMethodInfoMap
  else fstResource xs resourceMap resourceMethodsMap classMethodInfoMap
  with Not_found->(
    fstResource xs resourceMap resourceMethodsMap classMethodInfoMap
)
  ) 
  (*@result = fstResource keys resourceMap resourceMethodsMap classMethodInfoMap
      requires forall keys2. IntMap.mem keys2 resourceMethodsMap ->
          forall values. List.mem values (resourceMethodsMap.IntMap.view keys2) ->
           values <> ""
      variant keys
      ensures forall resId. List.mem resId keys -> 
        exists res.
        IntMap.mem resId resourceMap && res = resourceMap.IntMap.view resId ->
          ResourceClass.isField resId && res.ResourceClass.nature ->
            forall k. IntMap.mem k resourceMap-> 
            exists resource2.
            IntMap.mem k resourceMap && resource2 = resourceMap.IntMap.view k ->
            res.ResourceClass.position <> k ->
            exists r1methods r2methods. 
            (r1methods = resourceMethodsMap.IntMap.view res.ResourceClass.position && IntMap.mem res.ResourceClass.position resourceMethodsMap) &&
            (r2methods = resourceMethodsMap.IntMap.view resource2.ResourceClass.position && IntMap.mem resource2.ResourceClass.position resourceMethodsMap ) &&
            (sub r1methods r2methods && methodCycle r2methods true res resource2 classMethodInfoMap ) ->
              exists newResource2. 
              newResource2 = result.IntMap.view resource2.ResourceClass.position &&
              IntMap.mem resource2.ResourceClass.position result && 
            newResource2.ResourceClass.guardedBy = res.ResourceClass.position



  *)


(*função que recebe os 3 mapas necessários para realizar as operações e processa as chaves do mapa dos recursos*)
let subsumption classMethodInfoMap resourceMethodsMap resourceMap= 
let rBindings = IntMap.bindings resourceMap in 
let keys = List.map (fun (k, _) -> k) rBindings in
let newResourceMap = fstResource keys resourceMap resourceMethodsMap classMethodInfoMap in 
newResourceMap
(*@result = subsumption classMethodInfoMap resourceMethodsMap resourceMap
   requires forall keys2. IntMap.mem keys2 resourceMethodsMap ->
          forall values. List.mem values (resourceMethodsMap.IntMap.view keys2) ->
           values <> ""
   ensures forall resId. IntMap.mem resId resourceMap -> 
    exists res.
        IntMap.mem resId resourceMap && res = resourceMap.IntMap.view resId ->
          ResourceClass.isField resId && res.ResourceClass.nature ->
            forall k. IntMap.mem k resourceMap-> 
            exists resource2.
            IntMap.mem k resourceMap && resource2 = resourceMap.IntMap.view k ->
            res.ResourceClass.position <> k ->
            exists r1methods r2methods. 
            (r1methods = resourceMethodsMap.IntMap.view res.ResourceClass.position && IntMap.mem res.ResourceClass.position resourceMethodsMap) &&
            (r2methods = resourceMethodsMap.IntMap.view resource2.ResourceClass.position && IntMap.mem resource2.ResourceClass.position resourceMethodsMap ) &&
            (sub r1methods r2methods && methodCycle r2methods true res resource2 classMethodInfoMap ) ->
              exists newResource2. 
              newResource2 = result.IntMap.view resource2.ResourceClass.position &&
              IntMap.mem resource2.ResourceClass.position result && 
            newResource2.ResourceClass.guardedBy = res.ResourceClass.position

    *)

(* Função semelhante à de baixo mas recebe um resourceGroup*)
let insertR label (rGroup:resourceGroup) rOperationsMap=
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
  let rGroup = rGroupVar() in
  let newRGroup = { id = counter; ropList = rGroup.ropList} in
  let newRGroup = add rop newRGroup in
  let newlist = list @ [newRGroup] in
  let newROperationsMap = IntMap.add label newlist rOperationsMap in
  newROperationsMap
(*@newROperationsMap = createNewRGroup label rOperationsMap counter rop list
  ensures exists newList.
    (newList = newROperationsMap.IntMap.view label && IntMap.mem label newROperationsMap) ->
    List.length list < List.length newList && 
    exists newRGroup.
    let rGroup = rGroupVar() in
    newRGroup = { id = counter; ropList = rGroup.ropList} &&
    List.mem newRGroup newList
*)

(* requires label => -1
   ensures result.view label = list*)
let insert (label:int) (rop:rOp) rOperationsMap counter=
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
      let rGroup = rGroupVar() in
      newRGroup = { id = counter; ropList = rGroup.ropList} &&
      List.mem newRGroup newList
      else 
      exists newList.
      (newList = newROperationsMap.IntMap.view label && IntMap.mem label newROperationsMap) ->
       List.length newList > 0 && 
        exists newRGroup.
        let rGroup = rGroupVar() in
        newRGroup = { id = counter; ropList = rGroup.ropList} &&
        List.mem newRGroup newList
      *)

  let [@logic] insertRO opCode label res rOperationsMap counter=
    let (ro:rOp)= {op = opCode; r = res} in
    insert label ro rOperationsMap counter
    (*@newROperationsMap = insertRO opCode label res rOperationsMap counter
       ensures let rop = {op = opCode; r = res} in
       if IntMap.mem label rOperationsMap then 
     exists list newList.
      list = rOperationsMap.IntMap.view label &&
      (newList = newROperationsMap.IntMap.view label && IntMap.mem label newROperationsMap) ->
      List.length list < List.length newList && 
      exists newRGroup.
      let rGroup = rGroupVar() in
      newRGroup = { id = counter; ropList = rGroup.ropList} &&
      List.mem newRGroup newList
      else 
      exists newList.
      (newList = newROperationsMap.IntMap.view label && IntMap.mem label newROperationsMap) ->
       List.length newList > 0 && 
        exists newRGroup.
        let rGroup = rGroupVar() in
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
(*@
    requires firstRead >= -1
    requires lastRead  >= -1
    requires lastWrite >= -1
    requires res >= 0
    requires counter >= 0

    (* Case 1: if firstRead = -1 or lastRead < lastWrite
       → one insertRO at lastWrite, counter increments by 1 *)
    ensures
      (firstRead = -1 \/ lastRead < lastWrite) ->
      let m, c = result in
      m = insertRO 7 lastWrite res rOperationsMap counter /\
      c = counter + 1

    (* Case 2: if lastWrite < lastRead and firstRead ≠ -1
       → firstReadORlastWrite is applied,
         then insertRO at lastRead,
         final counter is c0 + 1 *)
    ensures
      (lastWrite < lastRead /\ firstRead <> -1) ->
      let m0, c0 = firstReadORlastWrite firstRead lastWrite res rOperationsMap counter in
      let m1 = insertRO 7 lastRead res m0 c0 in
      let m, c = result in
      m = m1 /\ c = c0 + 1

    (* Case 3: otherwise (lastWrite = lastRead and firstRead ≠ -1)
       → no modification: result unchanged *)
    ensures
      (lastWrite = lastRead /\ firstRead <> -1) ->
      result = (rOperationsMap, counter)

    (* General: counter never decreases *)
    ensures let _, c = result in c >= counter
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
(*@
  (***************************************************************************)
  (*  Complete Coverage of Accesses by Lock Operations (RA → RO coverage)     *)
  (***************************************************************************)

  requires res >= 0
  requires access.Access.first      >= -1
  requires access.Access.firstRead  >= -1
  requires access.Access.lastRead   >= -1
  requires access.Access.firstWrite >= -1
  requires access.Access.lastWrite  >= -1
  requires counter >= 0

  (* No accesses ⇒ no changes *)
  ensures (access.Access.firstRead = -1 && access.Access.firstWrite = -1) ->
          result = (rOperationsMap, counter)

  (* Counter monotonicity *)
  ensures let _, c' = result in c' >= counter
  ensures (access.Access.firstRead <> -1 || access.Access.firstWrite <> -1) ->
          let _, c' = result in c' > counter

  (* Availability marker (op 1) whenever any access exists *)
  ensures (access.Access.firstRead <> -1 || access.Access.firstWrite <> -1) ->
          let m, _ = result in
          let l = access.Access.first in
          IntMap.mem l m &&
          (exists grps. grps = m.IntMap.view l &&
           exists g. List.mem g grps &&
           exists rop. rop.r = res && rop.op = 1 && getResult g.ropList rop)

  (* READ‑ONLY: READ (2) at firstRead *)
  ensures (access.Access.firstRead <> -1 && access.Access.firstWrite = -1) ->
          let m, _ = result in
          let l1 = access.Access.firstRead in
          IntMap.mem l1 m &&
          (exists grps1. grps1 = m.IntMap.view l1 &&
           exists g1. List.mem g1 grps1 &&
           exists rop1. rop1.r = res && rop1.op = 2 && getResult g1.ropList rop1)

  (* READ‑ONLY: RELEASE (7) at lastRead *)
  ensures (access.Access.firstRead <> -1 && access.Access.firstWrite = -1) ->
          let m, _ = result in
          let l2 = access.Access.lastRead in
          IntMap.mem l2 m &&
          (exists grps2. grps2 = m.IntMap.view l2 &&
           exists g2. List.mem g2 grps2 &&
           exists rop2. rop2.r = res && rop2.op = 7 && getResult g2.ropList rop2)

  (* WRITE present and (no read OR write starts before read): WRITE (4) at firstWrite *)
  ensures (access.Access.firstWrite <> -1 &&
           (access.Access.firstRead = -1 || access.Access.firstWrite < access.Access.firstRead)) ->
          let m, _ = result in
          let lw = access.Access.firstWrite in
          IntMap.mem lw m &&
          (exists grps. grps = m.IntMap.view lw &&
           exists g. List.mem g grps &&
           exists rop. rop.r = res && rop.op = 4 && getResult g.ropList rop)

  (* WRITE present and no read tail: RELEASE (7) at lastWrite *)
  ensures (access.Access.firstWrite <> -1 &&
           (access.Access.firstRead = -1 || access.Access.lastRead < access.Access.lastWrite)) ->
          let m, _ = result in
          let lEnd = access.Access.lastWrite in
          IntMap.mem lEnd m &&
          (exists grps. grps = m.IntMap.view lEnd &&
           exists g. List.mem g grps &&
           exists rop. rop.r = res && rop.op = 7 && getResult g.ropList rop)

  (* WRITE present and read tail exists: DOWNGRADE (6) at lastWrite *)
  ensures (access.Access.firstWrite <> -1 &&
           access.Access.firstRead <> -1 &&
           access.Access.lastWrite < access.Access.lastRead) ->
          let m, _ = result in
          let lDW = access.Access.lastWrite in
          IntMap.mem lDW m &&
          (exists grps. grps = m.IntMap.view lDW &&
           exists g. List.mem g grps &&
           exists rop. rop.r = res && rop.op = 6 && getResult g.ropList rop)

  (* WRITE present and read tail exists: RELEASE (7) at lastRead *)
  ensures (access.Access.firstWrite <> -1 &&
           access.Access.firstRead <> -1 &&
           access.Access.lastWrite < access.Access.lastRead) ->
          let m, _ = result in
          let lRR = access.Access.lastRead in
          IntMap.mem lRR m &&
          (exists grps. grps = m.IntMap.view lRR &&
           exists g. List.mem g grps &&
           exists rop. rop.r = res && rop.op = 7 && getResult g.ropList rop)

  (* READ precedes WRITE: SHARED_BEFORE_EXCLUSIVE (3) at firstRead *)
  ensures (access.Access.firstWrite <> -1 &&
           access.Access.firstRead <> -1 &&
           access.Access.firstRead < access.Access.firstWrite) ->
          let m, _ = result in
          let lr = access.Access.firstRead in
          IntMap.mem lr m &&
          (exists grps. grps = m.IntMap.view lr &&
           exists g. List.mem g grps &&
           exists rop. rop.r = res && rop.op = 3 && getResult g.ropList rop)

  (* READ precedes WRITE: UPGRADE (5) at firstWrite *)
  ensures (access.Access.firstWrite <> -1 &&
           access.Access.firstRead <> -1 &&
           access.Access.firstRead < access.Access.firstWrite) ->
          let m, _ = result in
          let lw = access.Access.firstWrite in
          IntMap.mem lw m &&
          (exists grps. grps = m.IntMap.view lw &&
           exists g. List.mem g grps &&
           exists rop. rop.r = res && rop.op = 5 && getResult g.ropList rop)

  (* READ precedes WRITE and lastRead < firstWrite: RELEASE (7) at lastWrite *)
  ensures (access.Access.firstWrite <> -1 &&
           access.Access.firstRead <> -1 &&
           access.Access.firstRead < access.Access.firstWrite &&
           access.Access.lastRead < access.Access.firstWrite) ->
          let m, _ = result in
          let lEnd = access.Access.lastWrite in
          IntMap.mem lEnd m &&
          (exists grps. grps = m.IntMap.view lEnd &&
           exists g. List.mem g grps &&
           exists rop. rop.r = res && rop.op = 7 && getResult g.ropList rop)

  (* READ precedes WRITE and lastRead < lastWrite: DOWNGRADE (6) at lastWrite *)
  ensures (access.Access.firstWrite <> -1 &&
           access.Access.firstRead <> -1 &&
           access.Access.firstRead < access.Access.firstWrite &&
           access.Access.lastRead < access.Access.lastWrite) ->
          let m, _ = result in
          let lDW = access.Access.lastWrite in
          IntMap.mem lDW m &&
          (exists grps. grps = m.IntMap.view lDW &&
           exists g. List.mem g grps &&
           exists rop. rop.r = res && rop.op = 6 && getResult g.ropList rop)

  (* READ precedes WRITE and lastRead < lastWrite: RELEASE (7) at lastRead *)
  ensures (access.Access.firstWrite <> -1 &&
           access.Access.firstRead <> -1 &&
           access.Access.firstRead < access.Access.firstWrite &&
           access.Access.lastRead < access.Access.lastWrite) ->
          let m, _ = result in
          let lRR = access.Access.lastRead in
          IntMap.mem lRR m &&
          (exists grps. grps = m.IntMap.view lRR &&
           exists g. List.mem g grps &&
           exists rop. rop.r = res && rop.op = 7 && getResult g.ropList rop)
*)

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

(* Função recursiva: Percorre as chaves do mapa recebidas como argumento e extrai o seu value*)
(* O seu value é um mapa que mapeia resources (ints) -> resourceAccess*)
(* Por fim ela chama a função getPair para cada chave*)
(*Pre : receber o raMap bem construido
  Pos : devolver o mapa dos resourceOperations bem construido relativos a este raMap*)
let computeBindings (raMap:Access.resourceAccess IntMap.t)=
  (*print_string "rOperations Map Generation compute Bindings \n";*)
  let bindingsAccess = IntMap.bindings raMap in
  let bindingsAccess = List.map (fun (k, _) -> k) bindingsAccess in
  let rOperationsMap = IntMap.empty in
  let counter = 0 in
  let newROperationsMap = getPair raMap bindingsAccess rOperationsMap counter in
  newROperationsMap
(*@
  (* Basic shape properties (kept from your original) *)

  ensures (forall k:int. not (IntMap.mem k raMap)) ->
          (forall l:int. not (IntMap.mem l result))

  ensures forall l:int.
            IntMap.mem l result ->
            exists k:int. IntMap.mem k raMap

  ensures forall k:int.
            IntMap.mem k raMap ->
            exists l:int. IntMap.mem l result

  (*** Availability marker (opcode 1) when there is any access ***)
  ensures forall r:int.
            IntMap.mem r raMap ->
            let ra = raMap.IntMap.view r in
            (ra.Access.firstRead <> -1 || ra.Access.firstWrite <> -1) ->
            let l = ra.Access.first in
            IntMap.mem l result &&
            (exists grps.
               grps = result.IntMap.view l /\
               exists g.
                 List.mem g grps /\
                 exists rop.
                   rop.r = r && rop.op = 1 && getResult g.ropList rop)

  (*** READ-ONLY: firstRead -> READ(2), lastRead -> RELEASE(7) ***)
  ensures forall r:int.
            IntMap.mem r raMap ->
            let ra = raMap.IntMap.view r in
            (ra.Access.firstRead <> -1 && ra.Access.firstWrite = -1) ->
            let l1 = ra.Access.firstRead in
            let l2 = ra.Access.lastRead in
            IntMap.mem l1 result &&
            (exists grps1.
               grps1 = result.IntMap.view l1 /\
               exists g1.
                 List.mem g1 grps1 /\
                 exists rop1.
                   rop1.r = r && rop1.op = 2 && getResult g1.ropList rop1) &&
            IntMap.mem l2 result &&
            (exists grps2.
               grps2 = result.IntMap.view l2 /\
               exists g2.
                 List.mem g2 grps2 /\
                 exists rop2.
                   rop2.r = r && rop2.op = 7 && getResult g2.ropList rop2)

  (*** WRITE present & (no read OR write starts before read): firstWrite -> WRITE(4) ***)
  ensures forall r:int.
            IntMap.mem r raMap ->
            let ra = raMap.IntMap.view r in
            (ra.Access.firstWrite <> -1 &&
             (ra.Access.firstRead = -1 || ra.Access.firstWrite < ra.Access.firstRead)) ->
            let lw = ra.Access.firstWrite in
            IntMap.mem lw result &&
            (exists grps.
               grps = result.IntMap.view lw /\
               exists g.
                 List.mem g grps /\
                 exists rop.
                   rop.r = r && rop.op = 4 && getResult g.ropList rop)

  (*** Read before Write: firstRead -> SHARED_BEFORE_EXCLUSIVE(3), firstWrite -> UPGRADE(5) ***)
  ensures forall r:int.
            IntMap.mem r raMap ->
            let ra = raMap.IntMap.view r in
            (ra.Access.firstWrite <> -1 &&
             ra.Access.firstRead <> -1 &&
             ra.Access.firstRead < ra.Access.firstWrite) ->
            let lr = ra.Access.firstRead in
            let lw = ra.Access.firstWrite in
            IntMap.mem lr result &&
            (exists grpsA.
               grpsA = result.IntMap.view lr /\
               exists gA.
                 List.mem gA grpsA /\
                 exists ropA.
                   ropA.r = r && ropA.op = 3 && getResult gA.ropList ropA) &&
            IntMap.mem lw result &&
            (exists grpsB.
               grpsB = result.IntMap.view lw /\
               exists gB.
                 List.mem gB grpsB /\
                 exists ropB.
                   ropB.r = r && ropB.op = 5 && getResult gB.ropList ropB)

  (*** After writes: close correctly ***)

  (* No read tail: lastWrite -> RELEASE(7) *)
  ensures forall r:int.
            IntMap.mem r raMap ->
            let ra = raMap.IntMap.view r in
            (ra.Access.firstWrite <> -1 &&
             (ra.Access.firstRead = -1 || ra.Access.lastRead < ra.Access.lastWrite)) ->
            let lw2 = ra.Access.lastWrite in
            IntMap.mem lw2 result &&
            (exists grps.
               grps = result.IntMap.view lw2 /\
               exists g.
                 List.mem g grps /\
                 exists rop.
                   rop.r = r && rop.op = 7 && getResult g.ropList rop)

  (* Read tail exists: lastWrite -> DOWNGRADE(6) and lastRead -> RELEASE(7) *)
  ensures forall r:int.
            IntMap.mem r raMap ->
            let ra = raMap.IntMap.view r in
            (ra.Access.firstWrite <> -1 &&
             ra.Access.firstRead <> -1 &&
             ra.Access.lastWrite < ra.Access.lastRead) ->
            let lw3 = ra.Access.lastWrite in
            let lr2 = ra.Access.lastRead in
            IntMap.mem lw3 result &&
            (exists grps1.
               grps1 = result.IntMap.view lw3 /\
               exists g1.
                 List.mem g1 grps1 /\
                 exists rop1.
                   rop1.r = r && rop1.op = 6 && getResult g1.ropList rop1) &&
            IntMap.mem lr2 result &&
            (exists grps2.
               grps2 = result.IntMap.view lr2 /\
               exists g2.
                 List.mem g2 grps2 /\
                 exists rop2.
                   rop2.r = r && rop2.op = 7 && getResult g2.ropList rop2)
*)

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