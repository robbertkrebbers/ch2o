let num_lines x =
  let oc = open_in x and i = ref 0 in
  begin
    try while true; do let _ = input_line oc in i := !i + 1 done
    with End_of_file -> close_in oc
  end; !i

let cats = [
  ("integer_coding.v", "types");
  ("integer_operations.v", "types");
  ("addresses.v", "memory");
  ("aliasing.v", "memory");
  ("architecture_spec.v", "frontend");
  ("architectures.v", "frontend");
  ("ars.v", "prelude");
  ("assoc.v", "prelude");
  ("base.v", "prelude");
  ("base_values.v", "memory");
  ("bits.v", "memory");
  ("cmap.v", "separation");
  ("collections.v", "prelude");
  ("contexts.v", "operational");
  ("countable.v", "prelude");
  ("ctrees.v", "separation");
  ("decidable.v", "prelude");
  ("error.v", "prelude");
  ("executable_complete.v", "executable");
  ("executable_sound.v", "executable");
  ("executable.v", "executable");
  ("expression_eval_smallstep.v", "operational");
  ("expression_eval.v", "operational");
  ("expressions.v", "operational");
  ("extraction.v", "frontend");
  ("fin_collections.v", "prelude");
  ("finite.v", "prelude");
  ("fin_map_dom.v", "prelude");
  ("fin_maps.v", "prelude");
  ("flat_cmap.v", "separation");
  ("fragmented.v", "memory");
  ("fresh_numbers.v", "prelude");
  ("frontend.v", "frontend");
  ("frontend_sound.v", "frontend");
  ("hashset.v", "prelude");
  ("interpreter.v", "frontend");
  ("lexico.v", "prelude");
  ("listset_nodup.v", "prelude");
  ("listset.v", "prelude");
  ("list.v", "prelude");
  ("mapset.v", "prelude");
  ("memory_basics.v", "memory");
  ("memory_map.v", "memory");
  ("memory_trees.v", "memory");
  ("memory.v", "memory");
  ("natmap.v", "prelude");
  ("natural_type_environment.v", "frontend");
  ("nmap.v", "prelude");
  ("numbers.v", "prelude");
  ("operations.v", "operational");
  ("option.v", "prelude");
  ("orders.v", "prelude");
  ("permission_bits.v", "memory");
  ("permissions.v", "separation");
  ("pmap.v", "prelude");
  ("pointer_bits.v", "memory");
  ("pointer_casts.v", "memory");
  ("pointers.v", "memory");
  ("prelude.v", "prelude");
  ("pretty.v", "prelude");
  ("proof_irrel.v", "prelude");
  ("references.v", "memory");
  ("refinement_preservation.v", "refinements");
  ("memory_injections.v", "refinements");
  ("refinement_classes.v", "refinements");
  ("refinements.v", "refinements");
  ("refinement_system.v", "refinements");
  ("separation_instances.v", "separation");
  ("separation.v", "separation");
  ("smallstep.v", "operational");
  ("statements.v", "operational");
  ("state.v", "operational");
  ("streams.v", "prelude");
  ("stringmap.v", "prelude");
  ("tactics.v", "prelude");
  ("type_classes.v", "prelude");
  ("type_environment.v", "types");
  ("type_preservation.v", "operational");
  ("types.v", "types");
  ("type_system_decidable.v", "operational");
  ("type_system.v", "operational");
  ("values.v", "memory");
  ("vector.v", "prelude");
  ("zmap.v", "prelude");
  ("addresses_refine.v", "refinements");
  ("pointers_refine.v", "refinements");
  ("pointer_bits_refine.v", "refinements");
  ("bits_refine.v", "refinements");
  ("permission_bits_refine.v", "refinements");
  ("base_values_refine.v", "refinements");
  ("values_refine.v", "refinements");
  ("memory_trees_refine.v", "refinements");
  ("memory_map_refine.v", "refinements");
  ("memory_refine.v", "refinements");
  ("operations_refine.v", "refinements");
  ("constant_propagation.v", "memory");
  ("permission_bits_separation.v", "separation");
  ("memory_trees_separation.v", "separation");
  ("memory_map_separation.v", "separation");
  ("values_separation.v", "separation");
  ("memory_separation.v", "separation");
  ("assertions.v", "separation")
  ];;

let get_table _ =
  Array.fold_left (fun res file ->
    if Filename.check_suffix file ".v" then begin
      try let cat = List.assoc file cats in
        let n = num_lines file in
        Hashtbl.replace res cat (n + try Hashtbl.find res cat with _ -> 0)
      with Not_found -> failwith (file ^ " not found")
    end; res
  ) (Hashtbl.create 100) (Sys.readdir ".");;

let _ =
  let total = ref 0 in
  Hashtbl.iter (fun cat n ->
    total := !total + n;
    print_string (cat ^ "\t" ^ string_of_int n ^ "\n");
  ) (get_table ());
  let parser_count = num_lines "parser/Main.ml" in
  total := !total + parser_count;
  print_string ("parser\t" ^ string_of_int parser_count ^ "\n");
  print_string ("Total\t" ^ string_of_int !total ^ "\n");;

