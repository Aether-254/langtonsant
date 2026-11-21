import PeriodicWordCheck12E

namespace LangtonsAnt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem checkNoWords_twelve_F : checkNoWordsRange 12 2560 512 = true := by decide +kernel

end LangtonsAnt

