import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1854 : checkSingleBlackFast (-60, -39) 19613 .east (21, 11) (5, -44) = true := by
  decide +kernel

end LangtonsAnt
