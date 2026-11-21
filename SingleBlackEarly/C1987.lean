import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1987 : checkSingleBlackFast (-70, -51) 21440 .north (37, 33) (-63, -25) = true := by
  decide +kernel

end LangtonsAnt
