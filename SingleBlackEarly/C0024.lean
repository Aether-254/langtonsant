import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0024 : checkSingleBlackFast (2, 0) 6093 .west (-2, 3) (-19, -3) = true := by
  decide +kernel

end LangtonsAnt
