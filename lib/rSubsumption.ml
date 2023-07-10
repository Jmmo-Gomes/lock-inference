open Resource
open Mapping
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



  
