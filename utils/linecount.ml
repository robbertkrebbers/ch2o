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
  ("architecture_spec.v", "abstract_c");
  ("architectures.v", "abstract_c");
  ("ars.v", "prelude");
  ("assoc.v", "prelude");
  ("base.v", "prelude");
  ("base_values.v", "memory");
  ("bits.v", "memory");
  ("cmap.v", "separation_mem");
  ("collections.v", "prelude");
  ("contexts.v", "core_c");
  ("countable.v", "prelude");
  ("ctrees.v", "separation_mem");
  ("decidable.v", "prelude");
  ("error.v", "prelude");
  ("executable_complete.v", "core_c");
  ("executable_sound.v", "core_c");
  ("executable.v", "core_c");
  ("expression_eval_smallstep.v", "core_c");
  ("expression_eval.v", "core_c");
  ("expression_eval_separation.v", "separation");
  ("expressions.v", "core_c");
  ("extraction.v", "abstract_c");
  ("fin_collections.v", "prelude");
  ("finite.v", "prelude");
  ("fin_map_dom.v", "prelude");
  ("fin_maps.v", "prelude");
  ("flat_cmap.v", "separation_mem");
  ("fragmented.v", "memory");
  ("frontend.v", "abstract_c");
  ("frontend_sound.v", "abstract_c");
  ("hashset.v", "prelude");
  ("interpreter.v", "abstract_c");
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
  ("natural_type_environment.v", "abstract_c");
  ("nmap.v", "prelude");
  ("numbers.v", "prelude");
  ("operations.v", "core_c");
  ("option.v", "prelude");
  ("orders.v", "prelude");
  ("permission_bits.v", "memory");
  ("permissions.v", "separationalg");
  ("pmap.v", "prelude");
  ("pointer_bits.v", "memory");
  ("pointer_casts.v", "memory");
  ("pointers.v", "memory");
  ("prelude.v", "prelude");
  ("pretty.v", "prelude");
  ("proof_irrel.v", "prelude");
  ("references.v", "memory");
  ("refinement_preservation.v", "refinements");
  ("memory_injections.v", "refinements_mem");
  ("refinement_classes.v", "refinements_mem");
  ("refinements.v", "refinements_mem");
  ("refinement_system.v", "refinements");
  ("separation_instances.v", "separationalg");
  ("separation.v", "separationalg");
  ("smallstep.v", "core_c");
  ("statements.v", "core_c");
  ("state.v", "core_c");
  ("streams.v", "prelude");
  ("stringmap.v", "prelude");
  ("optionmap.v", "prelude");
  ("tactics.v", "prelude");
  ("type_classes.v", "prelude");
  ("type_environment.v", "types");
  ("type_preservation.v", "core_c");
  ("types.v", "types");
  ("type_system_decidable.v", "core_c");
  ("type_system.v", "core_c");
  ("values.v", "memory");
  ("vector.v", "prelude");
  ("zmap.v", "prelude");
  ("addresses_refine.v", "refinements_mem");
  ("pointers_refine.v", "refinements_mem");
  ("pointer_bits_refine.v", "refinements_mem");
  ("bits_refine.v", "refinements_mem");
  ("permission_bits_refine.v", "refinements_mem");
  ("base_values_refine.v", "refinements_mem");
  ("values_refine.v", "refinements_mem");
  ("memory_trees_refine.v", "refinements_mem");
  ("memory_map_refine.v", "refinements_mem");
  ("memory_refine.v", "refinements_mem");
  ("operations_refine.v", "refinements");
  ("constant_propagation.v", "memory");
  ("permission_bits_separation.v", "separation_mem");
  ("memory_trees_separation.v", "separation_mem");
  ("memory_map_separation.v", "separation_mem");
  ("values_separation.v", "separation_mem");
  ("memory_separation.v", "separation_mem");
  ("assertions.v", "separation");
  ("axiomatic.v", "separation");
  ("axiomatic_graph.v", "separation");
  ("axiomatic_expressions_help.v", "separation");
  ("axiomatic_expressions.v", "separation");
  ("axiomatic_functions.v", "separation");
  ("axiomatic_simple.v", "separation");
  ("axiomatic_statements.v", "separation");
  ("axiomatic_sound.v", "separation");
  ("assignments.v", "core_c");
  ("assignments_separation.v", "separation");
  ("restricted_smallstep.v", "core_c");
  ("memory_singleton.v", "core_c");
  ("example_gcd.v", "separation");
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

