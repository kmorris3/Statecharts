machine Clock_Machine 
sees Clock_Context
variables now > "real current time"
          at >
          "stands for activation times and is the event−calender∈
             function that gives for every event element of evts, a set of activation
             times in the future
             Note∈  When one of the events has an empty time list the machine fails"


invariants
  @typeof_now "now ∈ ℕ"
  @typeof_at "at ∈ evts → ℙ(ℕ)"
  @domain_at "dom(at)=evts" 
  @define_events "∀e · (e ∈ evts ∧ at(e) ≠ ∅ ⇒ now ≤ min(at(e)))"

events
  event INITIALISATION
    then
      @init_now "now ≔ 0"
      @init_at "at ≔ at_init" 
  end

  event add > "Adds a new future activation time ntime in the calendar of events e"
    any e ntime 
    where
      @define_e "e ∈ dom(at)"
      @check_now "now < ntime" > "Geoff What happens if you allow the model to add events in the pass
                                  and then proof that the model never does"
    then
      @update_at "at(e) ≔ at(e) ∪ {ntime}"
  end

  event use >
  " Activtes an event e, at the current time now,
     if e has ben scheduled to this current time (now ∈ at(e));
     in this case we remove  the current time from the calender of e· "
    any e 
    where
      @define_e "e ∈ dom(at)"
      @check_now "now ∈ at(e)"
    then
      @general_update_at "at(e) ≔ at(e) ∖ {now}"
  end

  event tic >
  " Time progression, current time is increased to now+1"
    where
      @check_at "∀e · e ∈ dom(at) ∧ at(e) ≠ ∅ ⇒ now + 1 ≤ min(at(e))"
    then
      @update_now "now ≔  now + 1"
  end
end

