import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1997 : checkSingleBlackFast (-75, -47) 25529 .east (33, 21) (11, -56) = true := by
  decide +kernel

end LangtonsAnt
