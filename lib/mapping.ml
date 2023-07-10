
  open Resource

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