open Lib
open OUnit2
open Mapping


    let guardsTest = 
      let bindings = [1;2;3;4;5] in 
      let resourceMap = IntMap.empty in 
     
      let resource1 : Resource.ResourceClass.resource = {position = 1; ty = 12341; vis = 0; nature = false; whatIs= 3; guardedBy = 2; isParameter= true} in 
      let resource2 : Resource.ResourceClass.resource = {position = 2; ty = 12341; vis = 0; nature = true; whatIs= 3; guardedBy = 3; isParameter= true} in 
      let resource3 : Resource.ResourceClass.resource = {position = 3; ty = 12341; vis = 0; nature = false; whatIs= 3; guardedBy = 3; isParameter= true} in 
      let resource4 : Resource.ResourceClass.resource = {position = 4; ty = 12341; vis = 0; nature = false; whatIs= 3; guardedBy = 4; isParameter= false} in 
      let resource5 : Resource.ResourceClass.resource = {position = 5; ty = 12341; vis = 0; nature = false; whatIs= 3; guardedBy = 5; isParameter= false} in 

      let resourceMap = IntMap.add 1 resource1 resourceMap in
      let resourceMap = IntMap.add 2 resource2 resourceMap in 
      let resourceMap = IntMap.add 3 resource3 resourceMap in 
      let resourceMap = IntMap.add 4 resource4 resourceMap in 
      let resourceMap = IntMap.add 5 resource5 resourceMap in 

      let resourceMap = Guards.bindingsTrasverse bindings resourceMap in 
      let resource1Guard = (IntMap.find 1 resourceMap).guardedBy in 
      if resource1Guard = 3 then true else false


    let guardsTest2 = 
      let bindings = [1;2;3;4;5] in 
      let resourceMap = IntMap.empty in 
     
      let resource1 : Resource.ResourceClass.resource = {position = 1; ty = 12341; vis = 0; nature = false; whatIs= 3; guardedBy = 2; isParameter= true} in 
      let resource2 : Resource.ResourceClass.resource = {position = 2; ty = 12341; vis = 0; nature = true; whatIs= 3; guardedBy = 3; isParameter= true} in 
      let resource3 : Resource.ResourceClass.resource = {position = 3; ty = 12341; vis = 0; nature = false; whatIs= 3; guardedBy = 5; isParameter= true} in 
      let resource4 : Resource.ResourceClass.resource = {position = 4; ty = 12341; vis = 0; nature = false; whatIs= 3; guardedBy = 1; isParameter= false} in 
      let resource5 : Resource.ResourceClass.resource = {position = 5; ty = 12341; vis = 0; nature = false; whatIs= 3; guardedBy = 5; isParameter= false} in 

      let resourceMap = IntMap.add 1 resource1 resourceMap in
      let resourceMap = IntMap.add 2 resource2 resourceMap in 
      let resourceMap = IntMap.add 3 resource3 resourceMap in 
      let resourceMap = IntMap.add 4 resource4 resourceMap in 
      let resourceMap = IntMap.add 5 resource5 resourceMap in 

      let resourceMap = Guards.bindingsTrasverse bindings resourceMap in 
      let resource1Guard = (IntMap.find 1 resourceMap).guardedBy in 
      let resource2Guard = (IntMap.find 2 resourceMap).guardedBy in 
      let resource3Guard = (IntMap.find 3 resourceMap).guardedBy in 
      let resource4Guard = (IntMap.find 4 resourceMap).guardedBy in 
      if resource1Guard = 5 && resource2Guard = 5 && resource3Guard = 5 && resource4Guard = 5 then true else false


      let guardsTest3 = 
        let bindings = [1;2;3;4;5] in 
        let resourceMap = IntMap.empty in 
       
        let resource1 : Resource.ResourceClass.resource = {position = 1; ty = 12341; vis = 0; nature = false; whatIs= 3; guardedBy = 1; isParameter= true} in 
        let resource2 : Resource.ResourceClass.resource = {position = 2; ty = 12341; vis = 0; nature = true; whatIs= 3; guardedBy = 2; isParameter= true} in 
        let resource3 : Resource.ResourceClass.resource = {position = 3; ty = 12341; vis = 0; nature = false; whatIs= 3; guardedBy = 3; isParameter= true} in 
        let resource4 : Resource.ResourceClass.resource = {position = 4; ty = 12341; vis = 0; nature = false; whatIs= 3; guardedBy = 4; isParameter= false} in 
        let resource5 : Resource.ResourceClass.resource = {position = 5; ty = 12341; vis = 0; nature = false; whatIs= 3; guardedBy = 5; isParameter= false} in 
  
        let resourceMap = IntMap.add 1 resource1 resourceMap in
        let resourceMap = IntMap.add 2 resource2 resourceMap in 
        let resourceMap = IntMap.add 3 resource3 resourceMap in 
        let resourceMap = IntMap.add 4 resource4 resourceMap in 
        let resourceMap = IntMap.add 5 resource5 resourceMap in 
  
        let resourceMap = Guards.bindingsTrasverse bindings resourceMap in 
        let resource1Guard = (IntMap.find 1 resourceMap).guardedBy in 
        let resource2Guard = (IntMap.find 2 resourceMap).guardedBy in 
        let resource3Guard = (IntMap.find 3 resourceMap).guardedBy in 
        let resource4Guard = (IntMap.find 4 resourceMap).guardedBy in 
        let resource5Guard = (IntMap.find 5 resourceMap).guardedBy in 
        if resource1Guard = 1 && resource2Guard = 2 && resource3Guard = 3 && resource4Guard = 4 && resource5Guard = 5 then true else false
  
  
let guardsTests = "test suite for subsumeResource" >::: [
  "GuardsTest" >:: (fun _ -> assert_equal 
  true
  (guardsTest) ~printer:string_of_bool);
  "GuardsTest2" >:: (fun _ -> assert_equal 
  true
  (guardsTest2) ~printer:string_of_bool);
  "GuardsTest3" >:: (fun _ -> assert_equal 
  true
  (guardsTest3) ~printer:string_of_bool);

]

let _ = run_test_tt_main guardsTests