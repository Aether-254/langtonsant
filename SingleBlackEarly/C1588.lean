import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1588 : checkSingleBlackFast (-35, -14) 29267 .east (4, -13) (-36, -12) = true := by
  decide +kernel

end LangtonsAnt
