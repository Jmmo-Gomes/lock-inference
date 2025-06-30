(* Locking Inference Algorithm - Unified OCaml Implementation *)

(* Resource operation type *)

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

(* Method type *)

type 'a met = {mutable name: string;
}

let methodVar = {name = "" }

let methodConstruct n methodVar=
  methodVar.name <- n; methodVar 

(*let mapType =
  let resource = Resource.newResource in
  ResourceMap.add "1" resource methodVar.resourceMap
*)

(* Resource type *)

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
            ra.first = lfirst && ra.firstRead = lfirstRead && ra.lastRead = llastRead && ra.firstWrite = lfirstWrite && ra.lastWrite = llastWrite
            |_ -> false
          *)
        

let hasReadAccess rA= 
  rA.firstRead <> -1
  (*@ b = hasReadAccess rA
    ensures b -> rA.firstRead <> -1
  *)

let hasWriteAccess rA= 
  rA.firstWrite <> -1
  (*@ b = hasWriteAccess rA
    ensures b -> rA.firstWrite <> -1
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

(* Int and String maps *)

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
    (IntMap.mem resId newResourceMethodsMap && newResourceMethodsMap.IntMap.view resId = [] ) *)

(* Resource Subsumption *)

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

(* Resource Group *)

type resourceGroup = {
  id : int;
  ropList : rOp list
}

let roEqual ro1 =
  let ro2 = {op = 0; r = -1} in 
  ro1.op = ro2.op && ro1.r = ro2.r


let [@logic] rGroupVar () = { id = -1; ropList = []}

let setId id resGroup =
  let newResGroup = { id = id ; ropList = resGroup.ropList} in  
  newResGroup

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
  (rop1.Roperation.r <> rop2.Roperation.r || rop1.Roperation.op <> rop2.Roperation.op)

  let [@logic] remove (rOp: rOp) resGroup = 
    let newRopList = List.filter (diff rOp) resGroup.ropList in
    { id = resGroup.id; ropList = newRopList}
    (*@ rg = remove3 rOp resGroup
        ensures List.mem rOp rg.ropList = false*)

(* Resource Operations Map Generation *)

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

(* Guards *)

let rec changeGuard resourceMap resourceList finalGuard= 
  match resourceList with 
  | [] -> resourceMap
  | x :: xs -> 
    try let resource = IntMap.find x resourceMap in
      let newResource = ResourceClass.setGuard finalGuard resource in
      let resourceMap = IntMap.add x newResource resourceMap in
      changeGuard resourceMap xs finalGuard
    with Not_found ->(
      changeGuard resourceMap xs finalGuard
  )
  (*newResourceMap = changeGuard resourceMap resourceList finalGuard
    variant resourceList
    ensures forall x. List.mem x resourceList ->
      IntMap.mem x resourceMap ->
      exists resource. 
      resource = newResourceMap.IntMap.view x 
      resource.ResourceClass.guardedBy = finalGuard
  *)

let rec createResourceList resourceMap guard resourceList =
  try let (resource:ResourceClass.resource) = IntMap.find guard resourceMap in 
  if resource.ResourceClass.position <> resource.ResourceClass.guardedBy then 
    let resourceList = resourceList @ [resource.ResourceClass.position] in 
    createResourceList resourceMap resource.ResourceClass.guardedBy resourceList
  else resourceList, resource.ResourceClass.position
with Not_found -> (
  resourceList, guard
)
(*@newResourceList, newGuard = createResourceList resourceMap guard resourceList
  ensures IntMap.mem guard resourceMap ->
    let resource = resourceMap.IntMap.view guard in 
    resource.ResourceClass.position <> resource.ResourceClass.guardedBy -> 
      List.mem resource.ResourceClass.position newResourceList 

*)

let rec bindingsTrasverse bindings (resourceMap:ResourceClass.resource IntMap.t)= 
  match bindings with 
  | [] -> resourceMap
  | x :: xs -> 
    try let resource = IntMap.find x resourceMap in 
      let guard = resource.ResourceClass.guardedBy in 
      if guard <> x then 
        let resourceList = [x] in
        let resourceList, finalGuard = createResourceList resourceMap guard resourceList in 
        let resourceMap = changeGuard resourceMap resourceList finalGuard in 
        bindingsTrasverse xs resourceMap 
      else 
        bindingsTrasverse xs resourceMap 
    with Not_found -> (
      bindingsTrasverse xs resourceMap 
    )


let locks (resourceMap:ResourceClass.resource IntMap.t) =
  let bindings = IntMap.bindings resourceMap in 
  let bindings = List.map (fun (k, _) -> k) bindings in
  let resourceMap = bindingsTrasverse bindings resourceMap in
  resourceMap

(* Lock Generation *)

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

(* Parameter Grouping *)

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

(* Two PL *)

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


(* Pipeline orchestration *)

module ClassMethodInfoMap = Map.Make(String)


let pipeline (raMap:Resource.Access.resourceAccess IntMap.t) (resourceMap:ResourceClass.resource IntMap.t)= 
  print_string "pipeline \n";
  let (roMap:ResourceGroup.resourceGroup list IntMap.t) = ROperationsMapGeneration.computeBindings raMap in
  let roMap = ParameterGrouping.parameterGrouping roMap resourceMap in
  let roMap = TwoPL.twoPhaseLocking roMap in 
  roMap

let rec getAccessMap bindings classMethodInfoMap (resourceMap:ResourceClass.resource IntMap.t)= 
  match bindings with
  | [] -> ()
  | x :: xs -> (let map = ClassMethodInfoMap.find x classMethodInfoMap in
  print_string "RaMap: ";print_string x; print_string "\n";
  let roMap = pipeline map resourceMap in
  let (resourceMap:ResourceClass.resource IntMap.t) = Guards.locks resourceMap in
  let res = LockGeneration.lockGeneration roMap resourceMap map in 
  Printf.printf "res:  %b " res;
  getAccessMap xs classMethodInfoMap resourceMap)

let getBindings (classMethodInfoMap:Resource.Access.resourceAccess IntMap.t
ClassMethodInfoMap.t) resourceMethodsMap (resourceMap:ResourceClass.resource IntMap.t) = 
  print_string "getBindings \n";
  let bindings = ClassMethodInfoMap.bindings classMethodInfoMap in
  let bindings = List.map (fun (k, _) -> k) bindings in
  let newResourceMap = RSubsumption.subsumption classMethodInfoMap resourceMethodsMap resourceMap in 
  getAccessMap bindings classMethodInfoMap newResourceMap


let initialize (classMethodInfoMap:Resource.Access.resourceAccess Mapping.IntMap.t
Mapping.ClassMethodInfoMap.t) (resourceMethodsMap:string list Mapping.IntMap.t) 
(resourceMap:ResourceClass.resource IntMap.t) =
  print_string "initialize \n";
  getBindings classMethodInfoMap resourceMethodsMap resourceMap 