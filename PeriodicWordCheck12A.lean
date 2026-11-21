import PeriodicWordCheck10

namespace LangtonsAnt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem checkNoWords_twelve_A : checkNoWordsRange 12 0 512 = true := by decide +kernel

end LangtonsAnt
