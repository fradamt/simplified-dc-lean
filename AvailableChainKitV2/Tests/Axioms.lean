module
public import AvailableChainKitV2.DutyEmission
public import AvailableChainKitV2.DutyLinked
public import AvailableChainKitV2.EngineClock

/-! Kernel dependencies of the subset field-origin helper. -/

#print axioms AvailableChain.V2.Engine.clock_field_origin_of_subset

-- Duty engine: every new production theorem.
#print axioms AvailableChain.V2.D.Engine.mem_tick_seat_iff
#print axioms AvailableChain.V2.D.Engine.mem_tick_duty_iff
#print axioms AvailableChain.V2.D.Engine.mem_tick_of_duty
#print axioms AvailableChain.V2.D.Engine.ownSeats_bijSeat
#print axioms AvailableChain.V2.D.Engine.emits_bijSeat
#print axioms AvailableChain.V2.D.Engine.mem_tick_seat_toD_iff
#print axioms AvailableChain.V2.D.Engine.linked_singleton_iff
#print axioms AvailableChain.V2.D.Engine.seat_family_iff_representative_toD
#print axioms AvailableChain.V2.D.Engine.seat_equation_toD_of_family
