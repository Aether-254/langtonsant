import PeriodicWordCheck12D

namespace LangtonsAnt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem checkNoWords_twelve_E : checkNoWordsRange 12 2048 512 = true := by decide +kernel

end LangtonsAnt

