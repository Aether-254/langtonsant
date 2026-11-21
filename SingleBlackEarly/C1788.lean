import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1788 : checkSingleBlackFast (-54, -33) 19301 .east (18, 8) (2, -41) = true := by
  decide +kernel

end LangtonsAnt
