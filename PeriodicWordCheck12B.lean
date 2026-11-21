import PeriodicWordCheck12A

namespace LangtonsAnt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem checkNoWords_twelve_B : checkNoWordsRange 12 512 512 = true := by decide +kernel

end LangtonsAnt

