import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1909 : checkSingleBlackFast (-67, -39) 25113 .east (29, 17) (7, -52) = true := by
  decide +kernel

end LangtonsAnt
