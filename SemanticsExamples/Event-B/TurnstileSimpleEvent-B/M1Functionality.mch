machine M1Functionality 
refines 
 M0
sees 
 C1
variables 
 GATE  CARD_READER  MAIN_REGION  GateIn_Block  GateIn_Unblock  OnIn_Reset  OnIn_CardAccept 
invariants 
 @typeof_GATE "GATE ∈ GATE_STATES"  
 @typeof_CARD_READER "CARD_READER ∈ CARD_READER_STATES"  
 @superstateof_GATE "GATE ≠ GATE_NULL ⇔ MAIN_REGION = ON"  
 @superstateof_CARD_READER "CARD_READER ≠ CARD_READER_NULL ⇔ MAIN_REGION = ON"  
 @typeof_Block "GateIn_Block ∈ BOOL"  
 @typeof_Unblock "GateIn_Unblock ∈ BOOL"  
 @typeof_Reset "OnIn_Reset ∈ BOOL"  
 @typeof_CardAccept "OnIn_CardAccept ∈ BOOL" 
 @check_BLOCKED "GATE=BLOCKED ⇔ GateIn_Block=TRUE" 
 @check_UNBLOCKED "GATE=UNBLOCKED ⇔ GateIn_Unblock=TRUE"
 @Accept_Before_Unlocked "(CARD_READER = ACCEPT ∧ OnIn_CardAccept=FALSE) ⇒ (GATE = UNBLOCKED)"  > "This invariant uses OnIn_CardAccept=FALSE so assure that
 the transition BLOCKED2UNBLOCKED has taken place·
 With additional synchronization functionality we 
 should be able to write 
 CARD_READER = ACCEPT ⇒ GATE = UNBLOCKED "
events 
 event INITIALISATION  extended ordinary 
 then
  @init_GATE "GATE ≔ GATE_NULL" 
  @init_CARD_READER "CARD_READER ≔ CARD_READER_NULL" 
  @init_Block "GateIn_Block≔FALSE" 
  @init_Unblock "GateIn_Unblock≔FALSE" 
  @init_CardAccept "OnIn_CardAccept≔FALSE" 
  @init_Reset "OnIn_Reset≔FALSE" 
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
  @set_Block "GateIn_Block ≔ TRUE" 
  @set_Reset "OnIn_Reset ≔ FALSE" 
 end
 event CardIn  ordinary 
 where 
   @isin_READY "CARD_READER = READY"  
   @check_Reset "OnIn_Reset = FALSE"  > "NOT IN THE SCXML NEEDED FOR CORRECT BEHAVIOR
   IF IT IS NOT PRESENT NON−DETERMINISM ALLOWS FOR 
   MALFUCNTION OF THE SYSTEM"
 then
  @enter_READING "CARD_READER ≔ READING" 
 end
 event CardError  ordinary 
 where 
   @isin_READING "CARD_READER = READING"  
 then
  @enter_READY "CARD_READER ≔ READY" 
 end
 event CardOk  ordinary 
 where 
   @isin_READING "CARD_READER = READING"  
 then
  @enter_ACCEPT "CARD_READER ≔ ACCEPT" 
  @set_CardAccept "OnIn_CardAccept ≔ TRUE" 
 end
 event Ready  ordinary 
 where 
   @isin_ACCEPT "CARD_READER = ACCEPT"  
   @check_CardAccept "OnIn_CardAccept = FALSE"  > "NOT IN THE SCXML NEEDED FOR CORRECT BEHAVIOR 
   IF IT IS NOT PRESENT NON−DETERMINISM ALLOWS FOR 
   MALFUCNTION OF THE SYSTEM"
 then
  @enter_READY "CARD_READER ≔ READY" 
  @set_Reset "OnIn_Reset ≔ TRUE" 
 end
 event UNBLOCKED_OUT_TRANS  ordinary > "Handles unnamed transition with conditions"
 where 
   @isin_UNBLOCKED "GATE = UNBLOCKED"  
   @check_Reset "OnIn_Reset=TRUE"  
 then
  @enter_BLOCKED "GATE ≔ BLOCKED" 
  @set_Block "GateIn_Block ≔ TRUE" 
  @set_Reset "OnIn_Reset ≔ FALSE" 
  @set_Unblock "GateIn_Unblock ≔ FALSE" 
 end
 event BLOCKED_OUT_TRANS  ordinary > "Handles unnamed transition with conditions"
 where 
   @isin_BLOCKED "GATE = BLOCKED"  
   @check_CardAccept "OnIn_CardAccept=TRUE"  
 then
  @enter_UNBLOCKED "GATE ≔ UNBLOCKED" 
  @set_Unblock "GateIn_Unblock ≔ TRUE" 
  @set_CardAccept "OnIn_CardAccept ≔ FALSE" 
  @set_Block "GateIn_Block ≔ FALSE" 
 end
end
