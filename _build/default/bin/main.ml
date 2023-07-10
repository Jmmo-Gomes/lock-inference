open Lib

let rec stringListToInt l newL=
match l with
| [] -> newL
| x :: xs ->
  let newL = newL @ [int_of_string x] in
  stringListToInt xs newL


let () =
  let fich = open_in "/home/pmsalgado/Desktop/FCT/Dissertacao/lock-inference-algorithm/fich.txt" in
  let count = ref 0 in
  let res = ref 0 in
  let met = ref "" in
  let resId:int ref = ref 0 in
  let cla = ref "" in
  let ty = ref 0 in
  let visib = ref 0 in
  let r_or_m = ref 0 in
  let resWhatIs = ref 0 in
  let nature = ref false in
  let (classMethodInfoMap:Resource.Access.resourceAccess Mapping.IntMap.t Mapping.ClassMethodInfoMap.t ref) = ref Mapping.ClassMethodInfoMap.empty in
  let resourceMap = ref Mapping.IntMap.empty in 
  let resourceMethodsMap = ref Mapping.IntMap.empty in

 

  let rec build_list infile =
   try
        let line = input_line infile in
        line :: build_list(infile)
   with End_of_file ->
        close_in infile;
        [] in
  let rec print_list = function
   [] -> () 
   | e::l -> Printf.printf "%d " !count; print_string e ; print_string "\n";

 
let prefix = "class" in

   if String.starts_with ~prefix e then r_or_m := 1
   else if String.starts_with ~prefix:"resources" e then (count:= 0; r_or_m := 0; print_string "r_or_m = 0 \n")
   else if String.starts_with ~prefix:"method" e then (count:=2; r_or_m:= 1) else
   if String.starts_with ~prefix:"resource" e then (count:= 4; r_or_m:= 1) else 
  print_string " ";

  if !r_or_m = 1 then
    match !count with
   | 0 -> count := 1;
   | 1 -> cla:= e; count := 2;
   | 2 -> count:= 3;
   | 3 -> met:= e; count := 5; 
   | 4 -> count:= 5;
   | 5 -> res:= int_of_string e;count := 6;
   | 6 ->   let listLabels = stringListToInt (String.split_on_char ',' e) [] in
            let classAndMethod = String.concat "," [!cla; !met] in
            let a,b,c = Mapping.computeLine listLabels classAndMethod !res !classMethodInfoMap !resourceMap !resourceMethodsMap in classMethodInfoMap := a; resourceMap := b; resourceMethodsMap := c; count:= 0; r_or_m := 2;
   | _ -> print_string ""
  else
    if !r_or_m = 0 then
      match !count with
      | 0 -> count := 1;
      | 1 -> resId:= int_of_string e; count := 2;
      | 2 -> ty:= int_of_string e; count := 3 ; 
      | 3 -> nature := bool_of_string e; count := 4;
      | 4 -> visib := int_of_string e; count:= 5;
      | 5 -> print_string "5  aqui \n ";resWhatIs := int_of_string e; let a,b = Mapping.computeResource !resId !ty !visib !nature !resWhatIs !resourceMap !resourceMethodsMap in resourceMap := a; resourceMethodsMap := b; count:= 0; r_or_m := 2;
      | _ -> print_string ""
    else print_string "espaço \n";
  print_string "\n";
  print_list l in
  print_list(build_list(fich));
  (*Mapping.printResourceMap ();*)
  Pipeline.initialize !classMethodInfoMap !resourceMethodsMap !resourceMap