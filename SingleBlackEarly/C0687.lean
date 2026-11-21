import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0687 : checkSingleBlackFast (19, -11) 10376 .north (0, -2) (-24, 0) = true := by
  decide +kernel

end LangtonsAnt
