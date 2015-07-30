machine M0 
sees 
 M0_implicitContext
variables 
 SM0 
invariants 
 @typeof_SM0 "SM0 ∈ SM0_STATES"  
events 
 event INITIALISATION  ordinary 
 then
  @init_SM0 "SM0 ≔ ON_OFF" 
 end
 event OnOff  ordinary 
 any
  StartOn 
 where 
   @StartOn_type "StartOn ∈ BOOL"  
   @isin_ON_OFF "SM0 = ON_OFF"  
 end
 Statemachine "SM0" translation SINGLEVAR
 nodes
 	Initial "SM0_initial1" ,
 	State "ON_OFF"
 transitions
 	Transition elaborates M0·INITIALISATION
 		source M0·SM0·SM0_initial1 target M0·SM0·ON_OFF
 	end
 	Transition elaborates M0·OnOff
 		source M0·SM0·ON_OFF target M0·SM0·ON_OFF
 	parameters
 		StartOn ∈ "BOOL"
 	end
 end
end
