import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1445 : checkSingleBlackFast (-24, 2) 10744 .north (1, 0) (-27, -2) = true := by
  decide +kernel

end LangtonsAnt
