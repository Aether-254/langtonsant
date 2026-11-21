import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1841 : checkSingleBlackFast (-60, -34) 12628 .north (19, 11) (-45, -27) = true := by
  decide +kernel

end LangtonsAnt
