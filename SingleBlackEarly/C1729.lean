import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1729 : checkSingleBlackFast (-50, -23) 11992 .north (13, 5) (-39, -21) = true := by
  decide +kernel

end LangtonsAnt
