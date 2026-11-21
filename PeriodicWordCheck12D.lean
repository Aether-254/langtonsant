import PeriodicWordCheck12C

namespace LangtonsAnt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem checkNoWords_twelve_D : checkNoWordsRange 12 1536 512 = true := by decide +kernel

end LangtonsAnt

