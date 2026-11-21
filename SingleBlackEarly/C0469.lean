import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0469 : checkSingleBlackFast (12, 13) 9638 .north (1, -2) (-24, -13) = true := by
  decide +kernel

end LangtonsAnt
