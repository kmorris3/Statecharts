machine M2 
refines 
 M1
sees 
 M2_implicitContext
variables 
 GATE  CARD_READER  SM0  ON_OFF_SM1 
invariants 
 @typeof_GATE "GATE ∈ GATE_STATES"  
 @typeof_CARD_READER "CARD_READER ∈ CARD_READER_STATES"  
 @superstateof_GATE "GATE ≠ GATE_NULL ⇔ ON_OFF_SM1 = ON"  
 @superstateof_CARD_READER "CARD_READER ≠ CARD_READER_NULL ⇔ ON_OFF_SM1 = ON"  
events 
 event INITIALISATION  extended ordinary 
 then
  @init_GATE "GATE ≔ GATE_NULL" 
  @init_CARD_READER "CARD_READER ≔ CARD_READER_NULL" 
 end
 event OnOff  extended ordinary 
 refines
 M1·OnOff
 where 
   @isin_ON_OFF "SM0 = ON_OFF"  
 then
  @leave_GATE "GATE ≔ GATE_NULL" 
  @leave_CARD_READER "CARD_READER ≔ CARD_READER_NULL" 
 end
 event OffOn  extended ordinary 
 refines
 M1·OffOn
 then
  @enter_BLOCKED "GATE ≔ BLOCKED" 
  @enter_READY "CARD_READER ≔ READY" 
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
 end
 event CardOk  ordinary 
 where 
   @isin_BLOCKED "GATE = BLOCKED"  
   @isin_READING "CARD_READER = READING"  
 then
  @enter_UNBLOCKED "GATE ≔ UNBLOCKED" 
  @enter_ACCEPT "CARD_READER ≔ ACCEPT" 
 end
 event Reset  ordinary 
 where 
   @isin_UNBLOCKED "GATE = UNBLOCKED"  
   @isin_ACCEPT "CARD_READER = ACCEPT"  
 then
  @enter_BLOCKED "GATE ≔ BLOCKED" 
  @enter_READY "CARD_READER ≔ READY" 
 end
 event Unblock  ordinary 
 where 
   @isin_BLOCKED "GATE = BLOCKED"  
   @isin_READING "CARD_READER = READING"  
 then
  @enter_UNBLOCKED "GATE ≔ UNBLOCKED" 
  @enter_ACCEPT "CARD_READER ≔ ACCEPT" 
 end
 event Block  ordinary 
 where 
   @isin_UNBLOCKED "GATE = UNBLOCKED"  
   @isin_ACCEPT "CARD_READER = ACCEPT"  
 then
  @enter_BLOCKED "GATE ≔ BLOCKED" 
  @enter_READY "CARD_READER ≔ READY" 
 end
 Statemachine "SM0" translation SINGLEVAR
 nodes
 	Initial "SM0_initial1" ,
 	State "ON_OFF"
 		statemachines 
 			Statemachine "ON_OFF_SM1" translation MULTIVAR
 			nodes
 				State "OFF" ,
 				State "ON"
 					statemachines 
 						Statemachine "GATE" translation MULTIVAR
 						nodes
 							Initial "GATE_initial1" ,
 							State "BLOCKED" ,
 							State "UNBLOCKED"
 						transitions
 							Transition elaborates M2·OffOn
 								source M2·SM0·ON_OFF·ON_OFF_SM1·ON·GATE·GATE_initial1 target M2·SM0·ON_OFF·ON_OFF_SM1·ON·GATE·BLOCKED
 							end
 							Transition elaborates M2·Unblock M2·CardOk
 								source M2·SM0·ON_OFF·ON_OFF_SM1·ON·GATE·BLOCKED target M2·SM0·ON_OFF·ON_OFF_SM1·ON·GATE·UNBLOCKED
 							end
 							Transition elaborates M2·Block M2·Reset
 								source M2·SM0·ON_OFF·ON_OFF_SM1·ON·GATE·UNBLOCKED target M2·SM0·ON_OFF·ON_OFF_SM1·ON·GATE·BLOCKED
 							end
 						end
 						Statemachine "CARD_READER" translation MULTIVAR
 						nodes
 							Initial "CARD_READER_initial1" ,
 							State "READY" ,
 							State "READING" ,
 							State "ACCEPT"
 						transitions
 							Transition elaborates M2·OffOn
 								source M2·SM0·ON_OFF·ON_OFF_SM1·ON·CARD_READER·CARD_READER_initial1 target M2·SM0·ON_OFF·ON_OFF_SM1·ON·CARD_READER·READY
 							end
 							Transition elaborates M2·CardIn
 								source M2·SM0·ON_OFF·ON_OFF_SM1·ON·CARD_READER·READY target M2·SM0·ON_OFF·ON_OFF_SM1·ON·CARD_READER·READING
 							end
 							Transition elaborates M2·CardError
 								source M2·SM0·ON_OFF·ON_OFF_SM1·ON·CARD_READER·READING target M2·SM0·ON_OFF·ON_OFF_SM1·ON·CARD_READER·READY
 							end
 							Transition elaborates M2·CardOk M2·Unblock
 								source M2·SM0·ON_OFF·ON_OFF_SM1·ON·CARD_READER·READING target M2·SM0·ON_OFF·ON_OFF_SM1·ON·CARD_READER·ACCEPT
 							end
 							Transition elaborates M2·Reset M2·Block
 								source M2·SM0·ON_OFF·ON_OFF_SM1·ON·CARD_READER·ACCEPT target M2·SM0·ON_OFF·ON_OFF_SM1·ON·CARD_READER·READY
 							end
 						end
 					end ,
 				Initial "ON_OFF_sm1_initial1"
 			transitions
 				Transition elaborates M2·INITIALISATION
 					source M2·SM0·ON_OFF·ON_OFF_SM1·ON_OFF_sm1_initial1 target M2·SM0·ON_OFF·ON_OFF_SM1·OFF
 				end
 				Transition elaborates M2·OffOn
 					source M2·SM0·ON_OFF·ON_OFF_SM1·OFF target M2·SM0·ON_OFF·ON_OFF_SM1·ON
 				with
 					@StartOn "StartOn=FALSE" 
 				end
 				Transition elaborates M2·OnOff
 					source M2·SM0·ON_OFF·ON_OFF_SM1·ON target M2·SM0·ON_OFF·ON_OFF_SM1·OFF
 				with
 					@StartOn "StartOn=TRUE" 
 				end
 			end
 		end
 transitions
 	Transition elaborates M2·INITIALISATION
 		source M2·SM0·SM0_initial1 target M2·SM0·ON_OFF
 	end
 	Transition elaborates M2·OnOff
 		source M2·SM0·ON_OFF target M2·SM0·ON_OFF
 	end
 end
end
