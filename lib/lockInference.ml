
type 'a met = {mutable name: string;
}

let methodVar = {name = "" }

let methodConstruct n methodVar=
  methodVar.name <- n; methodVar 

(*let mapType =
  let resource = Resource.newResource in
  ResourceMap.add "1" resource methodVar.resourceMap
*)


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

