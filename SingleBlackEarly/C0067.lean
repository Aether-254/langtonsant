import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0067 : checkSingleBlackFast (-4, -5) 8359 .west (2, -5) (-24, -8) = true := by
  decide +kernel

end LangtonsAnt
