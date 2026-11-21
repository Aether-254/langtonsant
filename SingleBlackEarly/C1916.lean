import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1916 : checkSingleBlackFast (-67, -44) 19957 .east (31, 16) (8, -50) = true := by
  decide +kernel

end LangtonsAnt
