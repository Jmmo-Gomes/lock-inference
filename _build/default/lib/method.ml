
type 'a met = {mutable name: string;
}

let methodVar = {name = "" }

let methodConstruct n methodVar=
  methodVar.name <- n; methodVar 

(*let mapType =
  let resource = Resource.newResource in
  ResourceMap.add "1" resource methodVar.resourceMap
*)