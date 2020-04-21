type ('nonterminal, 'terminal) parse_tree =
  | Node of 'nonterminal * ('nonterminal, 'terminal) parse_tree list
  | Leaf of 'terminal

type ('nonterminal, 'terminal) symbol =
  | N of 'nonterminal
  | T of 'terminal

(* a curried function that takes rules and a nonterminal, and returns a list of lists of symbols *)
 let rec convert_rules rules nonterminal = match rules with
 | [] -> []
 | (nt,right_hand_side)::rest_rules when nt = nonterminal-> 
 right_hand_side :: convert_rules rest_rules nonterminal
 | (_,_)::rest_rules ->
 convert_rules rest_rules nonterminal;;

(* give the curried function convert_rules the rules of gram1 as the defined argument *)
 let convert_grammar gram1 = match gram1 with
 | (start_symbol,rules) ->
 let convert_rules_wrapper = convert_rules rules in
 (start_symbol,convert_rules_wrapper)

 (* recursively print the parse tree leaves from left to right *)
 (* since the input is a single node or a list, naive pattern matching does not work *)
 (* we have to define a local function *)
 let parse_tree_leaves tree =
 let rec parse_tree_helper = function
 | [] -> []
 | Leaf term :: rest_tree -> [term] @ parse_tree_helper rest_tree
 | Node (_, curr_tree) :: rest_tree -> parse_tree_helper curr_tree @ parse_tree_helper rest_tree
in parse_tree_helper [tree]

(* 3. make_matcher *)
let match_empty frag accept = accept frag
let match_nothing frag accept = None
;;

(* the idea of mutual recursive functions is from slides of TA Patricia Xiao *)
(* matcher keeps track of all the possible grammars, while match_one_rule focuses one grammar rule at a time *)
(* This function solves the following three problems raised in class:
1. recursion and concatenation:
	- when the match_one_rule sees a nonterminal, it calls matcher to check with all possible rules
	  meaning it checks with itself and also other rules
	- so recursion and concatenation are solved.
2. alternation:
	- for every possible rule, matcher calls match_one_rule to delve deep into that rule. If there is no such
	  matching, it returns None and matcher keeps on checking the next rule
	- this accomplishes alternation of rules.
*)

let rec matcher gram_func accept frag = function
| [] -> match_nothing frag accept
| hd::tl -> (match match_one_rule gram_func hd accept frag with 
    | None -> matcher gram_func accept frag tl
    | ok -> ok)

and match_one_rule gram_func rule accept frag = match rule with
| [] -> match_empty frag accept
| (T term)::rest -> (match frag with
					| [] -> match_nothing frag accept
					| hd::tl when hd = term -> match_one_rule gram_func rest accept tl
					| hd::_ -> match_nothing frag accept)

| (N nt)::rest -> (match frag with
					| [] -> match_nothing frag accept
					| _ -> let new_accept = match_one_rule gram_func rest accept
							and new_list = gram_func nt in
							matcher gram_func  new_accept frag new_list)
;;

let make_matcher = function
| (start_symbol, gram_func) -> (fun accept frag -> matcher gram_func accept frag (gram_func start_symbol) );;


(* 4. make_parser *)

(* adding backtracking to the matcher *)
(* note this would only work if the accept returns 'a list option *)
(* we need a special acceptor for making a parser *)
let rec matcher_bt gram_func accept frag = function
| [] -> match_nothing frag accept
| hd::tl -> (match match_one_rule_bt gram_func hd accept frag with 
    | None -> matcher_bt gram_func accept frag tl
    | Some s -> Some(hd::s) )
(*let rec matcher_bt gram_func accept list frag = function
| [] -> match_nothing frag accept []
| hd::tl -> (match match_one_rule_bt gram_func hd accept list frag with 
    | None -> matcher_bt gram_func accept [] frag tl
    | Some s ->  )*)

and match_one_rule_bt gram_func rule accept frag = match rule with
| [] -> match_empty frag accept
| (T term)::rest -> (match frag with
					| [] -> match_nothing frag accept
					| hd::tl when hd = term -> match_one_rule_bt gram_func rest accept tl
					| hd::_ -> match_nothing frag accept)

| (N nt)::rest -> (match frag with
					| [] -> match_nothing frag accept
					| _ -> let new_accept = match_one_rule_bt gram_func rest accept
							and new_list = gram_func nt in
              matcher_bt gram_func new_accept frag new_list)
;;

let make_matcher_bt = function
| (start_symbol, gram_func) -> 
  (fun accept frag -> matcher_bt gram_func accept frag (gram_func start_symbol));;

(* empty acceptor that only accepts empty list *)
let accept_empty = function
| [] -> Some []
| _ -> None ;;

(* for the following code, idea is taken from TA helper code *)

(* transforms a list of nonterminals and terminals to Leaves and Nodes *)
let rec rhs2children = function
| [] -> []
| T symbol :: rest -> (Leaf symbol) :: (rhs2children rest)
| N nt :: rest -> (Node (nt,[])) :: (rhs2children rest) ;;

(* filters out the Leaves from list *)
let rec get_nodes = function
| [] -> []
| Leaf _ :: rest -> rest
| Node (root,tree) :: rest -> Node (root,tree) :: rest ;;

(* Based on matcher backtracking, this transforms a ('nonterminal,'terminal) list list to
a parser tree in a dfs fashion *)
(* as looping is not allowed, we need two recursive functions, one keeps track of the current level *)
(* the other goes down on the current node *)

let rec dfs_tree root = function
| [] -> [],Node(root,[])
| curr_rhs :: remaining_rhs ->
  let children = rhs2children curr_rhs in

  let rec dfs_helper rhs = function
  | [] -> rhs,[]

  (* when the current node we want to expand on is a Leaf, we don't expand or use rhs *)
  (* simply recurse on the rest of the nodes *)
  | (Leaf lf) :: rest_children -> (*match dfs_helper rhs rest_children with
    | remaining_rhs,remaining_children -> 
      let curr_leaves = (Leaf lf)::remaining_children in 
      remaining_rhs, curr_leaves*)
    let (remaining_rhs,remaining_children) = dfs_helper rhs rest_children in
    remaining_rhs, (Leaf lf)::remaining_children

  (* when we encounter a node, we expand the node by calling dfs_tree *)
  (* we still need to consider the rest of the nodes by appending them to the tail *)
  | (Node(root,subtree))::rest_children -> 
    let (remaining_rhs,curr_node) = dfs_tree root rhs in
    let (remaining_rhs_2,rest_leaves) = dfs_helper remaining_rhs rest_children in
    remaining_rhs_2, curr_node::rest_leaves

  (* transform the current rhs to Nodes and Leafs, expand on the children *)
  in let (rest_rhs,subtree) = dfs_helper remaining_rhs children
  (* create a node with the subtree returned from dfs *)
  in rest_rhs, Node(root,subtree)
;;

(* the final wrapper function *)
let make_parser grammar frag = match grammar with
| (start_symbol, gram_func) ->
  let acceptor = accept_empty in 
    let rhs_list = make_matcher_bt (start_symbol,gram_func) acceptor frag in
      match rhs_list with 
        | None -> None
        | Some list -> let _,parser_tree = dfs_tree start_symbol list in Some (parser_tree)
;;


