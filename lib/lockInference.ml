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
      (IntMap.mem resId newResourceMethodsMap && newResourceMethodsMap.IntMap.view resId = [] ) *)

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
  (rop1.r <> rop2.r || rop1.op <> rop2.op)

  let [@logic] remove (rOp: rOp) resGroup = 
    let newRopList = List.filter (diff rOp) resGroup.ropList in
    { id = resGroup.id; ropList = newRopList}
    (*@ rg = remove3 rOp resGroup
        ensures List.mem rOp rg.ropList = false*)
      
