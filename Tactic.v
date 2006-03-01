(** finish **)

Ltac  finish := intros; auto; trivial; discriminate.


(** contradict
     with contradict H 
         H: ~A |-   B     gives       |-   A
         H: ~A |- ~ B     gives  H: B |-   A
         H:  A |-   B     gives       |- ~ A
         H:  A |-   B     gives       |- ~ A
         H:  A |- ~ B     gives  H: A |- ~ A
  **)

Ltac  contradict name := 
     let term := type of name in (
     match term with 
       (~_) => 
          match goal with 
            |- ~ _  => let x := fresh in
                     (intros x; case name; 
                      generalize x; clear x name;
                      intro name)
          | |- _    => case name; clear name
          end
     | _ => 
          match goal with 
            |- ~ _  => let x := fresh in
                    (intros x;  absurd term;
                       [idtac | exact name]; generalize x; clear x name;
                       intros name)
          | |- _    => generalize name; absurd term;
                       [idtac | exact name]; clear name
          end
     end).


Ltac case_eq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.
