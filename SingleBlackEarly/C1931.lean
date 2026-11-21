import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1931 : checkSingleBlackFast (-69, -41) 25217 .east (30, 18) (8, -53) = true := by
  decide +kernel

end LangtonsAnt
