machine M1 
refines 
 M0
sees 
 M1_implicitContext
variables 
 SM0  ON_OFF_SM1 
invariants 
 @typeof_ON_OFF_SM1 "ON_OFF_SM1 ∈ ON_OFF_SM1_STATES"  
 @superstateof_ON_OFF_SM1 "ON_OFF_SM1 ≠ ON_OFF_SM1_NULL ⇔ SM0 = ON_OFF"  
events 
 event INITIALISATION  extended ordinary 
 then
  @init_ON_OFF_SM1 "ON_OFF_SM1 ≔ OFF" 
 end
 event OnOff  ordinary 
 refines
 M0·OnOff
 where 
   @isin_ON "ON_OFF_SM1 = ON"  
 with
  @StartOn "StartOn=TRUE" 
 then
  @enter_OFF "ON_OFF_SM1 ≔ OFF" 
 end
 event OffOn  ordinary 
 refines
 M0·OnOff
 where 
   @isin_OFF "ON_OFF_SM1 = OFF"  
 with
  @StartOn "StartOn=FALSE" 
 then
  @enter_ON "ON_OFF_SM1 ≔ ON" 
 end
 Statemachine "SM0" translation SINGLEVAR
 nodes
 	Initial "SM0_initial1" ,
 	State "ON_OFF"
 		statemachines 
 			Statemachine "ON_OFF_SM1" translation MULTIVAR
 			nodes
 				State "OFF" ,
 				State "ON" ,
 				Initial "ON_OFF_sm1_initial1"
 			transitions
 				Transition elaborates M1·INITIALISATION
 					source M1·SM0·ON_OFF·ON_OFF_SM1·ON_OFF_sm1_initial1 target M1·SM0·ON_OFF·ON_OFF_SM1·OFF
 				end
 				Transition elaborates M1·OffOn
 					source M1·SM0·ON_OFF·ON_OFF_SM1·OFF target M1·SM0·ON_OFF·ON_OFF_SM1·ON
 				with
 					@StartOn "StartOn=FALSE" 
 				end
 				Transition elaborates M1·OnOff
 					source M1·SM0·ON_OFF·ON_OFF_SM1·ON target M1·SM0·ON_OFF·ON_OFF_SM1·OFF
 				with
 					@StartOn "StartOn=TRUE" 
 				end
 			end
 		end
 transitions
 	Transition elaborates M1·INITIALISATION
 		source M1·SM0·SM0_initial1 target M1·SM0·ON_OFF
 	end
 	Transition elaborates M1·OnOff
 		source M1·SM0·ON_OFF target M1·SM0·ON_OFF
 	end
 end
end
