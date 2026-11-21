import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2037 : checkSingleBlackFast (-78, -51) 13448 .north (27, 19) (-53, -35) = true := by
  decide +kernel

end LangtonsAnt
