module Clase06.Imp

open FStar.Mul

type var = string

type expr =
  | Var   : var -> expr
  | Const : int -> expr
  | Plus  : expr -> expr -> expr
  | Minus : expr -> expr -> expr
  | Times : expr -> expr -> expr
  | Eq    : expr -> expr -> expr

type stmt =
  | Assign : var -> expr -> stmt
  | IfZ    : expr -> stmt -> stmt -> stmt
  | Seq    : stmt -> stmt -> stmt
  | Skip   : stmt
  | While  : expr -> stmt -> stmt

type state = var -> int

let rec eval_expr (s : state) (e : expr) : int =
  match e with
  | Var x -> s x
  | Const n -> n
  | Plus  e1 e2 -> eval_expr s e1 + eval_expr s e2
  | Minus e1 e2 -> eval_expr s e1 - eval_expr s e2
  | Times e1 e2 -> eval_expr s e1 * eval_expr s e2
  | Eq e1 e2 -> if eval_expr s e1 = eval_expr s e2 then 0 else 1

let override (#a:eqtype) (#b:Type) (f : a -> b) (x:a) (y:b) : a -> b =
  fun z -> if z = x then y else f z

(* Relación de evaluación big step. *)
noeq
type runsto : (p:stmt) -> (s0:state) -> (s1:state) -> Type0 =
  | R_Skip : s:state -> runsto Skip s s
  | R_Assign : s:state -> #x:var -> #e:expr -> runsto (Assign x e) s (override s x (eval_expr s e))
  | R_Seq :
    #p:stmt -> #q:stmt ->
    #s:state -> #t:state -> #u:state ->
    runsto p s t -> runsto q t u -> runsto (Seq p q) s u
  | R_IfZ_True :
    #c:expr -> #t:stmt -> #e:stmt ->
    #s:state -> #s':state -> runsto t s s' ->
    squash (eval_expr s c == 0) ->
    runsto (IfZ c t e) s s'
  | R_IfZ_False :
    #c:expr -> #t:stmt -> #e:stmt ->
    #s:state -> #s':state -> runsto e s s' ->
    squash (eval_expr s c <> 0) ->
    runsto (IfZ c t e) s s'
  | R_While_True :
    #c:expr -> #b:stmt -> #s:state -> #s':state -> #s'':state ->
    runsto b s s' ->
    squash (eval_expr s c = 0) ->
    runsto (While c b) s' s'' ->
    runsto (While c b) s s''
  | R_While_False :
    #c:expr -> #b:stmt -> #s:state ->
    squash (eval_expr s c <> 0) ->
    runsto (While c b) s s

// Demostrar que esta regla es admisible, es decir, que
// podemos "asumir" que la tenemos para demostrar, pero no
// necesitamos analizarla cuando destruímos una prueba:
//
// | R_While :
//   #c:expr -> #b:stmt ->
//   #s:state -> #s':state ->
//   runsto (IfZ c (Seq b (While c b)) Skip) s s' ->
//   runsto (While c b) s s'
let r_while (#c:expr) (#b:stmt) (#s #s' : state) (pf : runsto (IfZ c (Seq b (While c b)) Skip) s s')
  : runsto (While c b) s s'
= match pf with
  | R_IfZ_True #_ #_ #_ #_ #_ pf_seq eq0 -> (
    match pf_seq with
    | R_Seq #_ #_ #_ #_ #_ pf_b pf_w ->
      R_While_True #c #b #s #_ #s' pf_b eq0 pf_w
  )
  | R_IfZ_False #_ #_ #_ #_ #_ _ neq0 -> (
    R_While_False #c #b #s neq0
  )

type cond = state -> bool

noeq
type hoare : (pre:cond) -> (p:stmt) -> (post:cond) -> Type0 =
  | H_Skip : pre:cond -> hoare pre Skip pre // {P} Skip {P}
  | H_Seq :
    #p:stmt -> #q:stmt ->
    #pre:cond -> #mid:cond -> #post:cond ->
    hoare pre p mid -> hoare mid q post ->
    hoare pre (Seq p q) post  // {pre} p {mid} /\ {mid} q {post}    ==>    {pre} p;q {post}
  | H_Assign : 
    #x:var -> #e:expr -> #post:cond ->
    hoare (fun s -> post (override s x (eval_expr s e))) (Assign x e) post
  | H_IfZ :
    #c:expr -> #t:stmt -> #e:stmt ->
    #pre:cond -> #post:cond ->
    hoare (fun s -> pre s && (eval_expr s c = 0)) t post ->
    hoare (fun s -> pre s && (eval_expr s c <> 0)) e post ->
    hoare pre (IfZ c t e) post
  | H_While :
    #c:expr -> #b:stmt -> #inv:cond ->
    hoare (fun s -> inv s && (eval_expr s c = 0)) b inv ->
    hoare inv (While c b) (fun s -> inv s && (eval_expr s c <> 0))

let rec hoare_ok (p:stmt) (pre:cond) (post:cond) (pf : hoare pre p post)
                 (s0 s1 : state) (e_pf : runsto p s0 s1)
  : Lemma (requires pre s0)
          (ensures  post s1)
= match pf with
  | H_Skip _ -> ()
  | H_Seq #p #q #pre #mid #post hpf hqf ->
    let R_Seq #p #q #_ #t #_ rp rq = e_pf in
    hoare_ok p pre mid hpf s0 t rp;
    hoare_ok q mid post hqf t s1 rq
  | H_Assign -> ()
  | H_IfZ ht he -> (
    match e_pf with
    | R_IfZ_True #c #t #_ #_ #_ rt _ ->
      hoare_ok t (fun s -> pre s && (eval_expr s c = 0)) post ht s0 s1 rt
    | R_IfZ_False #c #_ #e #_ #_ re _ ->
      hoare_ok e (fun s -> pre s && (eval_expr s c <> 0)) post he s0 s1 re
  )
  | H_While #c #b #inv hb -> (
    match e_pf with
    | R_While_True #_ #_ #_ #smid #_ rb #_ #rw ->
      hoare_ok b (fun s -> pre s && (eval_expr s c = 0)) inv hb s0 smid rb;
      hoare_ok (While c b) inv (fun s -> inv s && (eval_expr s c <> 0)) pf smid s1 rw
    | R_While_False _-> ()
  )

let st0 : state = fun _ -> 0

let test1 : hoare (fun _ -> true) (Assign "x" (Const 1)) (fun s -> s "x" = 1) =
  H_Assign

