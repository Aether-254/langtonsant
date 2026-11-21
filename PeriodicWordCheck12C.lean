import PeriodicWordCheck12B

namespace LangtonsAnt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem checkNoWords_twelve_C : checkNoWordsRange 12 1024 512 = true := by decide +kernel

end LangtonsAnt

