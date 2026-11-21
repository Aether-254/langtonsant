import PeriodicWordCheck12F

namespace LangtonsAnt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem checkNoWords_twelve_G : checkNoWordsRange 12 3072 512 = true := by decide +kernel

end LangtonsAnt

