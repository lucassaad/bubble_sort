(* begin hide *)
Require Import Arith List Lia.
Require Import Recdef.
Require Import Sorted.
Require Import Permutation.
(* end hide*)

(**
Este trabalho apresenta uma prova formal da correção do algoritmo de ordenação por borbulhamento (a função [bs] a seguir). A formalização foi feita no assistente de provas Coq. O assistente de provas Coq utiliza o sistema de Dedução Natural, o que o torna adequado para o desenvolvimento de atividades computacionais no curso de Lógica Computacional 1. O Coq permite a extração de código certificado em diversas linguagens funcionais, como Ocaml, Haskell e Scheme. *)

(** Iniciaremos definindo a função [bubble] que recebe uma lista de naturais como argumento, e percorre esta lista comparando elementos consecutivos. Chamamos este processo de borbulhamento: *)

Function bubble (l: list nat ) {measure length l} :=
  match l with
  | nil => nil
  | x::nil => x::nil
  | x::y::l =>
      if x <=? y
      then x::(bubble (y::l))
            else y::(bubble (x::l))
            end.
Proof.
  - auto.
  - auto.
Defined.

(** Observe que esta função não é estruturalmente recursiva porque, por exemplo, a lista [(x::l)] não é uma sublista da lista original [(x::y::l)]. Neste caso, utilizamos [Function] para construir esta função e precisamos fornecer a medida que decresce em cada chamada recursiva, além de provar que esta medida efetivamente decresce a cada chamada recursiva. Por exemplo, [bubble (2::1::nil)] retorna a lista [(1::2::nil)].

 *)

Eval compute in bubble (2::1::nil).

(**

<<
   = 1 :: 2 :: nil
     : list nat
>>

*)

Eval compute in bubble (3::2::1::nil).

(**

<<
    = 2 :: 1 :: 3 :: nil
     : list nat
>>

*)

(** A função principal, ou seja, o algoritmo bubble sort propriamente dito, é dada pela função [bs] abaixo que recebe uma lista de naturais como argumento:

*)

Fixpoint bs (l: list nat) :=
  match l with
  | nil => nil
  | h::l' => bubble (h::(bs l'))
  end.           
(* begin hide *)
Eval compute in (bs (1::2::nil)).
Eval compute in (bs (2 :: 1::nil)).
Eval compute in (bs (3 :: 2 :: 1::nil)).
(* end hide *)

(** Sabemos que aplicar a função [bubble] a uma lista qualquer, não necessariamente vai retornar uma lista ordenada, mas o lema [bubble_sorted] a seguir nos mostra que se o primeiro elemento é o único elemento fora de ordem em uma lista, ao aplicarmos a função [bubble], obtemos uma lista ordenada: *)

Lemma bubble_sorted: forall l, Sorted le l -> bubble l = l.
Proof. Admitted.
  
Lemma bs_sorted: forall l, Sorted le (bs l).
Proof. Admitted.

(** A seguir, mostraremos que o algoritmo bubblesort (função [bs]) gera como saída uma permutação da lista de entrada. O lema a seguir nos diz que a função [bubble] também gera uma permutação da entrada: *)

Lemma bubble_perm: forall l, Permutation l (bubble l).
Proof.
  intro l.
  (* Introduz a variável l do forall no contexto. 
     Agora l é uma lista concreta (arbitrária, mas fixa),
     e o goal vira: Permutation l (bubble l) *)

  functional induction (bubble l).
  (* Usa o princípio de indução gerado automaticamente pelo Function
     que definiu bubble. Isso quebra a prova em 4 casos (subgoals),
     um para cada "ramo" da definição de bubble (nil / x::nil /
     x::y::l0 com x<=?y=true / x::y::l0 com x<=?y=false).
     Nos casos recursivos, o Coq já injeta no contexto a hipótese
     de indução correspondente à chamada recursiva. *)

  - (* CASO 1: l = nil
       Goal: Permutation nil nil *)
    apply perm_nil.
    (* perm_nil é o construtor que prova diretamente que nil é
       permutação de nil. Fecha o goal sem deixar nada pendente. *)

  - (* CASO 2: l = x::nil
       Goal: Permutation (x::nil) (x::nil) *)
    apply perm_skip.
    (* perm_skip: forall x l l', Permutation l l' -> Permutation (x::l) (x::l').
       Como os dois lados começam com o mesmo x, o Coq casa esse
       padrão e troca o goal por sua premissa: Permutation nil nil *)
    apply perm_nil.
    (* Agora o goal é Permutation nil nil, resolvido igual ao caso 1. *)

  - (* CASO 3: l = x::y::l0, com (x <=? y) = true
       Contexto tem: IHl0 : Permutation (y::l0) (bubble (y::l0))
       Goal: Permutation (x::y::l0) (x::bubble (y::l0)) *)
    apply perm_skip.
    (* Os dois lados do goal começam com o mesmo x.
       perm_skip "descasca" esse x dos dois lados.
       Novo goal: Permutation (y::l0) (bubble (y::l0)) *)
    apply IHl0.
    (* Esse novo goal é EXATAMENTE a hipótese de indução IHl0
       que já estava no contexto (foi gerada pelo functional induction
       para a chamada recursiva bubble (y::l0)).
       Não precisamos provar nada do zero: só reaproveitar IHl0. *)

  - (* CASO 4: l = x::y::l0, com (x <=? y) = false
       Contexto tem: IHl0 : Permutation (x::l0) (bubble (x::l0))
       Goal: Permutation (x::y::l0) (y::bubble (x::l0))
       Este caso é mais complexo porque a "cabeça" muda de x para y,
       então perm_skip sozinho não serve.*)
    apply perm_trans with (l' := y :: x :: l0).
    + (* subgoal 1: Permutation (x::y::l0) (y::x::l0) *)
      apply perm_swap.
    + (* subgoal 2: Permutation (y::x::l0) (y::bubble(x::l0)) *)
      apply perm_skip.
      apply IHl0.
Qed.

(** O lema [bs_correto] a seguir, nos mostra que o algoritmo [bs] gera uma permutação da lista de entrada: *)

Lemma bs_permuta: forall l, Permutation l (bs l).
Proof. Admitted.

(** Por fim, a correção do algoritmo [bs] é obtida pelo teorema a seguir que estabelece que o algoritmo [bs] retorna uma permutação da lista de entrada que está ordenada: *)
    
Theorem bs_correto: forall l, Sorted le (bs l) /\ Permutation l (bs l).
Proof.
Admitted.  

Check bubble_equation.
Check bubble_ind.

(** Repositório: %\url{https://github.com/flaviodemoura/bubble_sort}% *)
