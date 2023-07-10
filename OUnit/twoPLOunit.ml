open Lib
open OUnit2
open Mapping
open Roperation
open ResourceGroup

let ropListTrasverseTest =
  let key = 2 in 
  let lastlock = 8 in 
  let rop1 = {op = 4; r = 2} in 
  let rop2 = {op = 5; r = 3} in 
  let rop3 = {op = 3; r = 4} in 
  let rop4 = {op = 4; r = 5} in 
  let rop5 = {op = 7; r = 6} in 

  let rGroup1 ={id = 1; ropList = [rop1; rop2;rop3;rop4;rop5]} in 
  let rGroupSet = [rGroup1] in

  let roMap = IntMap.empty in 
  let roMap = IntMap.add key rGroupSet roMap in 

  let roMap = TwoPL.ropListTrasverse [rop1; rop2;rop3;rop4;rop5] roMap key rGroup1 lastlock rGroupSet in 

  if IntMap.mem 9 roMap then true else false

let ropListTrasverseTest2 =
  let key = 2 in 
  let lastlock = 8 in 
  let rop1 = {op = 4; r = 2} in 
  let rop2 = {op = 5; r = 3} in 
  let rop3 = {op = 3; r = 4} in 
  let rop4 = {op = 4; r = 5} in 
  let rop5 = {op = 7; r = 6} in 

  let rGroup1 ={id = 1; ropList = [rop1; rop2;rop3;rop4;rop5]} in 
  let rGroupSet = [rGroup1] in

  let roMap = IntMap.empty in 
  let roMap = IntMap.add key rGroupSet roMap in 

  let roMap = TwoPL.ropListTrasverse [rop1; rop2;rop3;rop4;rop5] roMap key rGroup1 lastlock rGroupSet in 

  if IntMap.mem key roMap then false else true

  let ropListTrasverseTest3 =
    let key = 2 in 
    let lastlock = 8 in 
    let rop1 = {op = 4; r = 2} in 
    let rop2 = {op = 5; r = 3} in 
    let rop3 = {op = 3; r = 4} in 
    let rop4 = {op = 4; r = 5} in 
    let rop5 = {op = 7; r = 6} in 
  
    let rGroup1 ={id = 1; ropList = [rop4;rop5]} in 
    let rGroup2 = {id = 2; ropList = [rop1; rop2;rop3;]} in
    let rGroupSet = [rGroup1;rGroup2] in
  
    let roMap = IntMap.empty in 
    let roMap = IntMap.add key rGroupSet roMap in 
  
    let roMap = TwoPL.ropListTrasverse [rop4;rop5] roMap key rGroup1 lastlock rGroupSet in 
  
    if IntMap.mem key roMap then true else false

  let lastLockTest = 
    let keys = [1;3;5] in 
    let lastlock = -1 in 

    let rop1 = {op = 4; r = 2} in 
    let rop2 = {op = 5; r = 3} in 
    let rop3 = {op = 3; r = 4} in 
    let rop4 = {op = 4; r = 5} in 
    let rop5 = {op = 7; r = 6} in 

    let rGroup1 = {id = 1; ropList = [rop1;rop2]} in 
    let rGroup2 = {id = 2; ropList = [rop3]} in 
    let rGroup3 = {id = 3; ropList = [rop4]} in 
    let rGroup4 = {id = 4; ropList = [rop5]} in 
    
    let rGroupSet1 = [rGroup1;rGroup2] in 
    let rGroupSet2 = [rGroup3] in 
    let rGroupSet3 = [rGroup4] in 

    let roMap = IntMap.empty in 
    let roMap = IntMap.add 1 rGroupSet1 roMap in 
    let roMap = IntMap.add 3 rGroupSet2 roMap in 
    let roMap = IntMap.add 5 rGroupSet3 roMap in 

    let lastlock = TwoPL.iterate keys roMap lastlock in 
    if lastlock =  3 then true else false 

    let lastLockTest2 = 
      let keys = [1;3;5] in 
      let lastlock = -1 in 
  
      let rop1 = {op = 4; r = 2} in 
      let rop2 = {op = 5; r = 3} in 
      let rop3 = {op = 3; r = 4} in 
      let rop4 = {op = 4; r = 5} in 
      let rop5 = {op = 2; r = 6} in 
  
      let rGroup1 = {id = 1; ropList = [rop1;rop2]} in 
      let rGroup2 = {id = 2; ropList = [rop3]} in 
      let rGroup3 = {id = 3; ropList = [rop4]} in 
      let rGroup4 = {id = 4; ropList = [rop5]} in 
      
      let rGroupSet1 = [rGroup1;rGroup2] in 
      let rGroupSet2 = [rGroup3] in 
      let rGroupSet3 = [rGroup4] in 
  
      let roMap = IntMap.empty in 
      let roMap = IntMap.add 1 rGroupSet1 roMap in 
      let roMap = IntMap.add 3 rGroupSet2 roMap in 
      let roMap = IntMap.add 5 rGroupSet3 roMap in 
  
      let lastlock = TwoPL.iterate keys roMap lastlock in 
      if lastlock =  5 then true else false 

      let lastLockTest3 = 
        let keys = [1;3;5] in 
        let lastlock = -1 in 
    
        let rop1 = {op = 4; r = 2} in 
        let rop2 = {op = 5; r = 3} in 
        let rop3 = {op = 3; r = 4} in 
        let rop4 = {op = 4; r = 5} in 
        let rop5 = {op = 1; r = 6} in 
        let rop6 = {op = 2; r = 6} in 
    
        let rGroup1 = {id = 1; ropList = [rop1;rop2]} in 
        let rGroup2 = {id = 2; ropList = [rop3]} in 
        let rGroup3 = {id = 3; ropList = [rop4]} in 
        let rGroup4 = {id = 4; ropList = [rop5]} in 
        let rGroup5 = {id = 5; ropList = [rop6]} in 
        
        let rGroupSet1 = [rGroup1;rGroup2] in 
        let rGroupSet2 = [rGroup3] in 
        let rGroupSet3 = [rGroup4; rGroup5] in 
    
        let roMap = IntMap.empty in 
        let roMap = IntMap.add 1 rGroupSet1 roMap in 
        let roMap = IntMap.add 3 rGroupSet2 roMap in 
        let roMap = IntMap.add 5 rGroupSet3 roMap in 
    
        let lastlock = TwoPL.iterate keys roMap lastlock in 
        if lastlock =  5 then true else false 

let twoPLTests = "test suite for subsumeResource" >::: [
  "ropListTrasverseTest -new entry but RGroupSet not empty" >:: (fun _ -> assert_equal 
  true
  (ropListTrasverseTest) ~printer:string_of_bool);
  "ropListTrasverseTest2 - RGroupSet empty so entry is deleted" >:: (fun _ -> assert_equal 
  true
  (ropListTrasverseTest2) ~printer:string_of_bool);
  "ropListTrasverseTest2 - RGroupSet not empty so entry is not deleted" >:: (fun _ -> assert_equal 
  true
  (ropListTrasverseTest3) ~printer:string_of_bool);
  "lastLockTest - lastlock is in rGroup3 with 3 as a key" >:: (fun _ -> assert_equal 
  true
  (lastLockTest) ~printer:string_of_bool);
  "lastLockTest2 - lastlock is in rGroup3 with 5 as a key" >:: (fun _ -> assert_equal 
  true
  (lastLockTest2) ~printer:string_of_bool);
  "lastLockTest3 - lastlock is in rGroup5 with 5 as a key" >:: (fun _ -> assert_equal 
  true
  (lastLockTest3) ~printer:string_of_bool);
]

let _ = run_test_tt_main twoPLTests
