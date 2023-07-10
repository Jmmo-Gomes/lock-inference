open Mapping
open Resource

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
  



