machine M2 
refines 
 M1
sees 
 C2
variables 
 GATE  CARD_READER  MAIN_REGION  Block  Unblock  now  at  READY_REGION  timed_COMPLETE_SET_UP_Label  timed_CLEAR_Label 
invariants 
 @typeof_READY_REGION "READY_REGION ∈ READY_STATES"  
 @superstateof_READY_REGION "READY_REGION ≠ READY_NULL ⇔ CARD_READER = READY"  
 @typeof_timed_CLEAR_Label "timed_CLEAR_Label ∈ BOOL"  
 @typeof_timed_COMPLETE_SET_UP_Label "timed_COMPLETE_SET_UP_Label ∈ BOOL"  
events 
 event INITIALISATION  extended ordinary 
 then
  @init_timed_COMPLETE_SET_UP_Label "timed_COMPLETE_SET_UP_Label ≔ TRUE" 
  @init_timed_CLEAR_Label "timed_CLEAR_Label ≔ TRUE" 
  @init_READY_REGION "READY_REGION ≔ READY_NULL" 
 end
 event OnOff_OFF  extended ordinary 
 refines
 M1·OnOff_OFF
 then
   @leave_READY_REGION "READY_REGION ≔ READY_NULL"
 end
 event OnOff_ON  extended ordinary 
 refines
 M1·OnOff_ON
 then
  @enter_CLEAR "READY_REGION ≔ CLEAR" >
  "I should ¬ be allowed to trigger the timed_CLEAR event with an 
   previous value for the time·  There should be a way to reset the clock 
   @clear_timed_CLEAR at(timed_CLEAR)≔∅"
 end
 event CardIn  extended ordinary 
 refines
 M1·CardIn
 where 
   @isin_READY_FINAL "READY_REGION = READY_FINAL"  
 then
  @leave_READY_REGION "READY_REGION ≔ READY_NULL" 
 end
 event CardError  extended ordinary 
 refines
 M1·CardError
 then
  @enter_CLEAR "READY_REGION ≔ CLEAR" 
 end
 event CardOk  extended ordinary 
 refines
 M1·CardOk
 end
 event Reset  extended ordinary 
 refines
 M1·Reset
 then
   @enter_CLEAR "READY_REGION ≔ CLEAR" > 
  " To clear any old information in the clock event map
   @clear_timed_CLEAR at(timed_CLEAR)≔∅
   @clear_timed_COMPLETE_SET_UP at(timed_COMPLETE_SET_UP)≔∅"
 end
 event UNBLOCKED_OUT_TRANS  extended ordinary > "Handles unnamed transition with conditions· Can be removed"
 refines
 M1·UNBLOCKED_OUT_TRANS
 end
 event BLOCKED_OUT_TRANS  extended ordinary > "Handles unnamed transition with conditions· Can be removed"
 refines
 M1·BLOCKED_OUT_TRANS
 end
 event add_timed_CLEAR  ordinary 
 refines
 M1·add
 where  
   @define_e "timed_CLEAR ∈ dom(at)"  
   @check_now "now < now+t_relative_CLEAR" 
   @check_t_CLEAR "at(timed_CLEAR)=∅"
   @isin_CLEAR "READY_REGION = CLEAR"  
 with
  @e "e=timed_CLEAR" 
  @ntime "ntime = now+t_relative_CLEAR" 
 then 
 @update_at "at(timed_CLEAR) ≔ at(timed_CLEAR) ∪ {now+t_relative_CLEAR}" 
 end
 event add_timed_COMPLETE_SET_UP  ordinary 
 refines
 M1·add
 where 
   @define_e "timed_COMPLETE_SET_UP ∈ dom(at)"  
   @check_now "now < now+t_relative_COMPLETE_SET_UP" 
   @check_t_COMPLETE_SET_UP "at(timed_COMPLETE_SET_UP)=∅" 
   @isin_CLEAR "READY_REGION = COMPLETE_SET_UP"  
 with
  @e "e=timed_COMPLETE_SET_UP" 
  @ntime "ntime = now+t_relative_COMPLETE_SET_UP" 
 then
  @update_at "at(timed_COMPLETE_SET_UP) ≔ at(timed_COMPLETE_SET_UP) ∪ {now+t_relative_COMPLETE_SET_UP}" 
 end
 event use_timed_CLEAR  ordinary 
 refines
 M1·use
 where 
   @define_e "timed_CLEAR ∈ dom(at)"  
   @check_now "now ∈ at(timed_CLEAR)"  
   @cheack_timed_CLEAR "timed_CLEAR_Label = TRUE"  
   @isin_CLEAR "READY_REGION=CLEAR"  
 with
  @e "e=timed_CLEAR" 
 then
  @general_update_at "at(timed_CLEAR) ≔ at(timed_CLEAR) ∖ {now}" 
  @update_timed_CLEAR_Label "timed_CLEAR_Label ≔ FALSE" 
  @enter_COMPLETE_SET_UP "READY_REGION ≔ COMPLETE_SET_UP" 
 end
 event use_timed_COMPLETE_SET_UP  ordinary 
 refines
 M1·use
 where 
   @define_e "timed_COMPLETE_SET_UP ∈ dom(at)"  
   @check_now "now ∈ at(timed_COMPLETE_SET_UP)"  
   @cheack_timed_CLEAR "timed_COMPLETE_SET_UP_Label = TRUE"  
   @isin_CLEAR "READY_REGION=COMPLETE_SET_UP"  
 with
  @e "e=timed_COMPLETE_SET_UP" 
 then
  @general_update_at "at(timed_COMPLETE_SET_UP) ≔ at(timed_COMPLETE_SET_UP) ∖ {now}" 
  @update_timed_CLEAR_Label "timed_COMPLETE_SET_UP_Label ≔ FALSE" 
  @enter_COMPLETE_SET_UP "READY_REGION ≔ READY_FINAL" 
 end
 event tic  extended ordinary 
 refines
 M1·tic
 where 
   @check_timed_CLEAR_Label "(timed_CLEAR_Label = FALSE) ∨  (timed_CLEAR_Label = TRUE ∧ ¬ now∈at(timed_CLEAR)) "  
   @check_timed_COMPLETE_SET_UP_Label "(timed_COMPLETE_SET_UP_Label = FALSE) ∨ (timed_COMPLETE_SET_UP_Label = TRUE ∧ ¬ now∈at(timed_COMPLETE_SET_UP)) "  
 then
  @reset_timed_CLEAR_Label "timed_CLEAR_Label ≔ TRUE" 
  @reset_timed_COMPLETE_SET_UP_Label "timed_COMPLETE_SET_UP_Label ≔ TRUE" 
 end
end
