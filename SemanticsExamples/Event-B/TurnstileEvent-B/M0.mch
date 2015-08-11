machine M0 
refines 
 Clock_Machine
sees 
 C0
variables 
 MAIN_REGION  at  now 
invariants 
 @typeof_MAIN_REGION "MAIN_REGION ∈ MAIN_REGION_STATES"  
events 
 event INITIALISATION  extended ordinary 
 then
  @init_MAIN_REGION "MAIN_REGION≔OFF" 
 end
 event OnOff  ordinary 
 any
  s 
 where 
   @typeof_s "s ∈ dom(OnOff_MAP) ∧ s=MAIN_REGION"  
   @isin_ON_OFF "MAIN_REGION=ON ∨ MAIN_REGION=OFF"  
 then
  @enter_OFF_ON "MAIN_REGION≔OnOff_MAP(s)" 
 end
 event add  extended ordinary 
 refines
 Clock_Machine·add
 end
 event use  ordinary 
 refines
 Clock_Machine·use
 end
 event tic  extended ordinary 
 refines
 Clock_Machine·tic
 end
end
