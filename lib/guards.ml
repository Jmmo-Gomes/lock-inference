open Mapping
open Resource

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
  

   
  

