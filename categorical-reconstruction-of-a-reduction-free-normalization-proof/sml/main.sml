(* val nf = fn : Ty list -> Ty -> Tm -> Tm *)

infixr -->;

datatype Ty = O | --> of Ty * Ty;

type Co = Ty list;

datatype Tm = var0 | varS of Tm | lam of Tm | app of Tm * Tm;

datatype Wk = w_id | w1 of Wk | w2 of Wk;

val w_pi = w1(w_id);

fun o_wk w_id w = w
    | o_wk (w1 w) w' = w1(o_wk w w')
    | o_wk (w2 w) w_id = w2(w)
    | o_wk (w2 w) (w1 w') = w1(o_wk w w')
    | o_wk (w2 w) (w2 w') = w2(o_wk w w');

fun wk_tm w_id M = M
    | wk_tm w (lam M) = lam (wk_tm (w2 w) M)
    | wk_tm w (app (M1, M2)) = app(wk_tm w M1, wk_tm w M2)
    | wk_tm (w2 w) (varS M) = wk_tm w M
    | wk_tm (w2 w) var0 = var0
    | wk_tm (w1 w) M = varS (wk_tm w M);

datatype Vl = v_o of Tm | v_arr of Wk->Vl->Vl;

fun wk_vl w (v_o M) = v_o (wk_tm w M)
    | wk_vl w (v_arr f) = v_arr (fn w' => fn x => f (o_wk w w') x);

fun wk_vls w xs = map (wk_vl w) xs;

fun q O (v_o M) = M
    | q (S --> T) (v_arr f) = lam (q T (f w_pi (u S var0)))
    and u O M = v_o M
        | u (S --> T) M = v_arr(fn w => fn x => (u T (app (wk_tm w M, q S x))));

fun eval var0 (x::xs) = x
    | eval (varS M) (x::xs) = eval M xs
    | eval (lam M) xs = v_arr (fn w => fn x => eval M (x::(wk_vls w xs)))
    | eval (app (M1, M2)) xs =
      case (eval M1 xs) of
           (v_arr f) => f w_id (eval M2 xs);

fun id [] = []
    | id (S::G) = (u S var0)::(wk_vls w_pi (id G));

fun nf G S M = q S (eval M (id G));