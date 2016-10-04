theory "Ids"
imports Complex_Main
begin
(*Differential dynamic logic can be defined for any finite types, given a 
  few elements of those types (so that we can generate axioms). *)
locale ids =
  (* NOTE: 'sf, 'sz don't have to be finite *)
  fixes vid1 :: "('sz::{finite,linorder})"
  fixes vid2 :: 'sz
  fixes vid3 :: 'sz
  fixes fid1 :: "('sf::finite)"
  fixes fid2 :: 'sf
  fixes fid3 :: 'sf
  fixes pid1 :: "('sc::finite)"
  fixes pid2 :: 'sc
  fixes pid3 :: 'sc
  fixes pid4 :: 'sc
  assumes vne12:"vid1 \<noteq> vid2"
  assumes vne23:"vid2 \<noteq> vid3"
  assumes vne13:"vid1 \<noteq> vid3"
  assumes fne12:"fid1 \<noteq> fid2"
  assumes fne23:"fid2 \<noteq> fid3"
  assumes fne13:"fid1 \<noteq> fid3"
  assumes pne12:"pid1 \<noteq> pid2"
  assumes pne23:"pid2 \<noteq> pid3"
  assumes pne13:"pid1 \<noteq> pid3"
  assumes pne34:"pid3 \<noteq> pid4"
end