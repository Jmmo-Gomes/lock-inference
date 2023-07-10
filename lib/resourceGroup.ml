open Roperation

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
      
