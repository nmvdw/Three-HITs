Require Import HoTT.

(* Here we collect general facts about HITs in the HoTT library.
   We will then put the generally useful ones into the HoTT library. *)

(* Note: the coequalizers are already around, see
   http://hott.github.io/HoTT/proviola-html/HoTT.HIT.Colimits.Coequalizer.html *)

(* Note: the mapping telescope is already around, see
   https://ncatlab.org/nlab/show/mapping+telescope for naming,
   and http://hott.github.io/HoTT/proviola-html/HoTT.HIT.Colimits.MappingTelescope.html,
   although that file fails to actually define the relevant HIT, it just provides
   the graph for it. Perhaps we should re-define mapping telescopes directly, i.e.,
   just take the development from ColimsLem.v (that one should be broken down into
   seeral pieces.
*)