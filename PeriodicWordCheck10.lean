import PeriodicWordCheck8

namespace LangtonsAnt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem checkNoWords_ten : checkNoWords 10 = true := by decide +kernel

end LangtonsAnt
