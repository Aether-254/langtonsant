import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1942 : checkSingleBlackFast (-68, -47) 20029 .east (25, 15) (9, -48) = true := by
  decide +kernel

end LangtonsAnt
