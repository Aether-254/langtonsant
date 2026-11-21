import PeriodicWordCheck12G

namespace LangtonsAnt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem checkNoWords_twelve_H : checkNoWordsRange 12 3584 512 = true := by decide +kernel

end LangtonsAnt

