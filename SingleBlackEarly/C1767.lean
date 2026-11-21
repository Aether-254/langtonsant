import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1767 : checkSingleBlackFast (-50, -31) 20400 .north (27, 23) (-53, -15) = true := by
  decide +kernel

end LangtonsAnt
