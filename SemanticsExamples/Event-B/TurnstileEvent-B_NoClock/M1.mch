machine M1 
refines 
 M0
sees 
 C1
variables 
 GATE  CARD_READER  MAIN_REGION  GateIn_Block  GateIn_Unblock 
invariants 
 @typeof_GATE "GATE ∈ GATE_STATES"  
 @typeof_CARD_READER "CARD_READER ∈ CARD_READER_STATES"  
 @superstateof_GATE "GATE ≠ GATE_NULL ⇔ MAIN_REGION = ON"  
 @superstateof_CARD_READER "CARD_READER ≠ CARD_READER_NULL ⇔ MAIN_REGION = ON"  
 @typeof_Block "GateIn_Block ∈ BOOL"  
 @typeof_Unblock "GateIn_Unblock ∈ BOOL"  
 @Requirement_1_BLOCKED "GATE = BLOCKED ⇒ GateIn_Block = TRUE "  
 @Requirement_2_BLOCKED "GATE = BLOCKED ⇒ GateIn_Unblock = FALSE"  
 @Requirement_1_UNBLOCKED "GATE = UNBLOCKED ⇒ GateIn_Block = FALSE "  
 @Requirement_2_UNBLOCKED "GATE = UNBLOCKED ⇒ GateIn_Unblock = TRUE"  
 @Requirement_1_READY "CARD_READER = READY ⇒ GateIn_Block = TRUE "  
 @Requirement_2_READY "CARD_READER = READY ⇒ GateIn_Unblock = FALSE"  
 @Requirement_1_ACCEPT "CARD_READER = ACCEPT ⇒ GateIn_Block = FALSE "  
 @Requirement_2_ACCEPT "CARD_READER = ACCEPT ⇒ GateIn_Unblock = TRUE"  
events 
 event INITIALISATION  extended ordinary 
 then
  @init_GATE "GATE ≔ GATE_NULL" 
  @init_CARD_READER "CARD_READER ≔ CARD_READER_NULL" 
  @typeof_Block "GateIn_Block≔FALSE" 
  @typeof_Unblock "GateIn_Unblock≔FALSE" 
 end
 event OnOff_OFF  extended ordinary 
 refines
 M0·OnOff
 where 
   @isin_ON "MAIN_REGION = ON"  
 then
  @leave_GATE "GATE ≔ GATE_NULL" 
  @leave_CARD_READER "CARD_READER ≔ CARD_READER_NULL" 
  @set_Unblock "GateIn_Unblock ≔ FALSE" 
  @set_Block "GateIn_Block ≔ FALSE" 
 end
 event OnOff_ON  extended ordinary 
 refines
 M0·OnOff
 where 
   @isin_OFF "MAIN_REGION = OFF"  
 then
  @enter_BLOCKED "GATE ≔ BLOCKED" 
  @enter_READY "CARD_READER ≔ READY" 
  @set_Unblock "GateIn_Unblock ≔ FALSE" 
  @set_Block "GateIn_Block ≔ TRUE" 
 end
 event CardIn  ordinary 
 where 
   @isin_READY "CARD_READER = READY"  
 then
  @enter_READING "CARD_READER ≔ READING" 
 end
 event CardError  ordinary 
 where 
   @isin_READING "CARD_READER = READING"  
 then
  @enter_READY "CARD_READER ≔ READY" 
  @set_Unblock "GateIn_Unblock ≔ FALSE" 
  @set_Block "GateIn_Block ≔ TRUE" 
  @enter_BLOCKED "GATE ≔ BLOCKED" > "This should always be the case· "
 end
 event CardOk  ordinary 
 where 
   @isin_READING "CARD_READER = READING"  
 then
  @set_Unblock "GateIn_Unblock ≔ TRUE" 
  @set_Block "GateIn_Block ≔ FALSE" 
  @enter_ACCEPT "CARD_READER ≔ ACCEPT" 
  @enter_UNBLOCKED "GATE ≔ UNBLOCKED" > "This should be an action that triggers the
Event BLOCKED_OUT_TRANS
As it is now this requires human input"
 end
 event Reset  ordinary 
 where 
   @isin_ACCEPT "CARD_READER = ACCEPT"  
 then
  @set_Unblock "GateIn_Unblock ≔ FALSE" 
  @set_Block "GateIn_Block ≔ TRUE" 
  @enter_READY "CARD_READER ≔ READY" 
  @enter_BLOCKED "GATE ≔ BLOCKED" > "This should be an action that triggers the
Event UNBLOCKED_OUT_TRANS  As it is now this requires human input "
 end
 event UNBLOCKED_OUT_TRANS  ordinary > "Handles unnamed transition with conditions"
 where 
   @isin_UNBLOCKED "GATE = UNBLOCKED"  
   @check_Block "GateIn_Unblock=TRUE"  
 then
  @enter_BLOCKED "GATE ≔ BLOCKED" 
  @set_Unblock "GateIn_Unblock ≔ FALSE" 
  @set_Block "GateIn_Block ≔ TRUE" > "Need to add raise Reset some how· Short way is to copy actions, but this isn't always the desire behavior·"
 end
 event BLOCKED_OUT_TRANS  ordinary > "Handles unnamed transition with conditions"
 where 
   @isin_BLOCKED "GATE = BLOCKED"  
   @check_Unblock "GateIn_Block=TRUE"  
 then
  @enter_UNBLOCKED "GATE ≔ UNBLOCKED" 
  @set_Unblock "GateIn_Unblock ≔ TRUE" 
  @set_Block "GateIn_Block ≔ FALSE" 
 end
end
