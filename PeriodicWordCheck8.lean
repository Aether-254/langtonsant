import PeriodicWordEnumeration

namespace LangtonsAnt

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem checkNoWords_two : checkNoWords 2 = true := by decide +kernel
theorem checkNoWords_four : checkNoWords 4 = true := by decide +kernel
theorem checkNoWords_six : checkNoWords 6 = true := by decide +kernel
theorem checkNoWords_eight : checkNoWords 8 = true := by decide +kernel

end LangtonsAnt
